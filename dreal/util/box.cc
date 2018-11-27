#include "dreal/util/box.h"

#include <algorithm>
#include <cmath>
#include <functional>
#include <limits>
#include <utility>

#include "dreal/util/assert.h"
#include "dreal/util/exception.h"
#include "dreal/util/logging.h"
#include "dreal/util/math.h"

using std::ceil;
using std::equal;
using std::find_if;
using std::floor;
using std::make_pair;
using std::make_shared;
using std::numeric_limits;
using std::ostream;
using std::pair;
using std::unordered_map;
using std::vector;

namespace dreal {

Box::Box()
    : variables_{make_shared<vector<Variable>>()},
      // We have this hack here because it is not allowed to have a
      // zero interval vector. Note that because of this special case,
      // `variables_->size() == values_.size()` do not hold. We should
      // rely on `values_.size()`.
      values_{1},
      var_to_idx_{
          make_shared<unordered_map<Variable, int, hash_value<Variable>>>()},
      idx_to_var_{make_shared<unordered_map<int, Variable>>()} {}

Box::Box(const vector<Variable>& variables)
    : variables_{make_shared<vector<Variable>>()},
      values_{static_cast<int>(variables.size())},
      var_to_idx_{
          make_shared<unordered_map<Variable, int, hash_value<Variable>>>()},
      idx_to_var_{make_shared<unordered_map<int, Variable>>()} {
  for (const Variable& var : variables) {
    Add(var);
  }
}

void Box::Add(const Variable& v) {
  // Duplicate variables are not allowed.
  DREAL_ASSERT(find_if(variables_->begin(), variables_->end(),
                       [&v](const Variable& var) { return v.equal_to(var); }) ==
               variables_->end());

  if (!variables_.unique()) {
    // If the components of this box is shared by more than one
    // entity, we need to clone this before adding the variable `v`
    // so that these changes remain local.
    variables_ = make_shared<vector<Variable>>(*variables_);
    var_to_idx_ =
        make_shared<unordered_map<Variable, int, hash_value<Variable>>>(
            *var_to_idx_);
    idx_to_var_ = make_shared<unordered_map<int, Variable>>(*idx_to_var_);
  }
  const int n{size()};
  idx_to_var_->emplace(n, v);
  var_to_idx_->emplace(v, n);
  variables_->push_back(v);
  values_.resize(size());

  // Set up Domain.
  // TODO(soonho): For now, we allow Boolean variables in a box. Change this.
  if (v.get_type() == Variable::Type::BOOLEAN ||
      v.get_type() == Variable::Type::BINARY) {
    values_[n] = Interval(0.0, 1.0);
  } else if (v.get_type() == Variable::Type::INTEGER) {
    values_[n] =
        Interval(-numeric_limits<int>::max(), numeric_limits<int>::max());
  }
}

void Box::Add(const Variable& v, const double lb, const double ub) {
  Add(v);

  DREAL_ASSERT(lb <= ub);

  // Binary variable => lb, ub ∈ [0, 1].
  DREAL_ASSERT(v.get_type() != Variable::Type::BINARY ||
               (0.0 <= lb && ub <= 1.0));

  // Integer variable => lb, ub ∈ Z.
  DREAL_ASSERT(v.get_type() != Variable::Type::INTEGER ||
               (is_integer(lb) && is_integer(ub)));

  values_[(*var_to_idx_)[v]] = Interval{lb, ub};
}

bool Box::empty() const { return values_.is_empty(); }

void Box::set_empty() { values_.set_empty(); }

int Box::size() const { return variables_->size(); }

Box::Interval& Box::operator[](const int i) {
  DREAL_ASSERT(i < size());
  return values_[i];
}
Box::Interval& Box::operator[](const Variable& var) {
  return values_[(*var_to_idx_)[var]];
}
const Box::Interval& Box::operator[](const int i) const {
  DREAL_ASSERT(i < size());
  return values_[i];
}
const Box::Interval& Box::operator[](const Variable& var) const {
  return values_[(*var_to_idx_)[var]];
}

const vector<Variable>& Box::variables() const { return *variables_; }

const Variable& Box::variable(const int i) const { return (*idx_to_var_)[i]; }

bool Box::has_variable(const Variable& var) const {
  return var_to_idx_->count(var) > 0;
}

int Box::index(const Variable& var) const { return (*var_to_idx_)[var]; }

const Box::IntervalVector& Box::interval_vector() const { return values_; }
Box::IntervalVector& Box::mutable_interval_vector() { return values_; }

pair<double, int> Box::MaxDiam() const {
  double max_diam{0.0};
  int idx{-1};
  for (size_t i{0}; i < variables_->size(); ++i) {
    const double diam_i{values_[i].diam()};
    if (diam_i > max_diam && values_[i].is_bisectable()) {
      max_diam = diam_i;
      idx = i;
    }
  }
  return make_pair(max_diam, idx);
}

pair<Box, Box> Box::bisect(const int i) const {
  const Variable& var{(*idx_to_var_)[i]};
  if (!values_[i].is_bisectable()) {
    throw DREAL_RUNTIME_ERROR(
        "Variable {} = {} is not bisectable but Box::bisect is called.", var,
        values_[i]);
  }
  switch (var.get_type()) {
    case Variable::Type::CONTINUOUS:
      return bisect_continuous(i);
    case Variable::Type::INTEGER:
      return bisect_int(i);
    case Variable::Type::BINARY:
      return bisect_int(i);
    case Variable::Type::BOOLEAN:
      DREAL_UNREACHABLE();
  }
  DREAL_UNREACHABLE();
}

pair<Box, Box> Box::bisect(const Variable& var) const {
  auto it = var_to_idx_->find(var);
  if (it != var_to_idx_->end()) {
    return bisect(it->second);
  } else {
    throw DREAL_RUNTIME_ERROR("Variable {} is not found in this box.", var);
  }
  return bisect((*var_to_idx_)[var]);
}

pair<Box, Box> Box::bisect_int(const int i) const {
  DREAL_ASSERT(idx_to_var_->at(i).get_type() == Variable::Type::INTEGER ||
               idx_to_var_->at(i).get_type() == Variable::Type::BINARY);
  const Interval& intv_i{values_[i]};
  const double lb{ceil(intv_i.lb())};
  const double ub{floor(intv_i.ub())};
  const double mid{intv_i.mid()};
  const double mid_floor{floor(mid)};
  DREAL_ASSERT(intv_i.lb() <= lb);
  DREAL_ASSERT(lb <= mid_floor);
  DREAL_ASSERT(mid_floor + 1 <= ub);
  DREAL_ASSERT(ub <= intv_i.ub());

  Box b1{*this};
  Box b2{*this};
  b1[i] = Interval(lb, mid_floor);
  b2[i] = Interval(mid_floor + 1, ub);
  return make_pair(b1, b2);
}

pair<Box, Box> Box::bisect_continuous(const int i) const {
  DREAL_ASSERT(idx_to_var_->at(i).get_type() == Variable::Type::CONTINUOUS);
  Box b1{*this};
  Box b2{*this};
  const Interval intv_i{values_[i]};
  pair<Interval, Interval> bisected_intervals{intv_i.bisect(0.5)};
  b1[i] = bisected_intervals.first;
  b2[i] = bisected_intervals.second;
  return make_pair(b1, b2);
}

Box& Box::InplaceUnion(const Box& b) {
  // Checks variables() == b.variables().
  DREAL_ASSERT(equal(variables().begin(), variables().end(),
                     b.variables().begin(), b.variables().end(),
                     std::equal_to<Variable>{}));
  values_ |= b.values_;
  return *this;
}

namespace {
// RAII which preserves the FmtFlags of an ostream.
class IosFmtFlagSaver {
 public:
  explicit IosFmtFlagSaver(ostream& os) : os_(os), flags_(os.flags()) {}
  ~IosFmtFlagSaver() { os_.flags(flags_); }

  IosFmtFlagSaver(const IosFmtFlagSaver& rhs) = delete;
  IosFmtFlagSaver(IosFmtFlagSaver&& rhs) = delete;
  IosFmtFlagSaver& operator=(const IosFmtFlagSaver& rhs) = delete;
  IosFmtFlagSaver& operator=(IosFmtFlagSaver&& rhs) = delete;

 private:
  ostream& os_;
  std::ios::fmtflags flags_;
};
}  // namespace

ostream& operator<<(ostream& os, const Box& box) {
  IosFmtFlagSaver saver{os};
  // See
  // https://stackoverflow.com/questions/554063/how-do-i-print-a-double-value-with-full-precision-using-cout#comment40126260_554134.
  os.precision(numeric_limits<double>::max_digits10 + 2);
  int i{0};
  for (const Variable& var : *(box.variables_)) {
    const Box::Interval interval{box.values_[i++]};
    os << var << " : ";
    switch (var.get_type()) {
      case Variable::Type::INTEGER:
      case Variable::Type::BINARY:
        if (interval.is_empty()) {
          os << "[ empty ]";
        } else {
          os << "[" << static_cast<int>(interval.lb()) << ", "
             << static_cast<int>(interval.ub()) << "]";
        }
        break;
      case Variable::Type::CONTINUOUS:
        os << interval;
        break;
      case Variable::Type::BOOLEAN:
        if (interval.ub() == 0.0) {
          os << "False";
        } else if (interval.lb() == 1.0) {
          os << "True";
        } else {
          os << "Unassigned";
        }
        break;
    }
    if (i != box.size()) {
      os << "\n";
    }
  }
  return os;
}

bool operator==(const Box& b1, const Box& b2) {
  return equal(b1.variables().begin(), b1.variables().end(),
               b2.variables().begin(), b2.variables().end(),
               std::equal_to<Variable>{}) &&
         (b1.interval_vector() == b2.interval_vector());
}

bool operator!=(const Box& b1, const Box& b2) { return !(b1 == b2); }

ostream& DisplayDiff(ostream& os, const vector<Variable>& variables,
                     const Box::IntervalVector& old_iv,
                     const Box::IntervalVector& new_iv) {
  IosFmtFlagSaver saver{os};
  // See
  // https://stackoverflow.com/questions/554063/how-do-i-print-a-double-value-with-full-precision-using-cout#comment40126260_554134.
  os.precision(numeric_limits<double>::max_digits10 + 2);
  for (size_t i = 0; i < variables.size(); ++i) {
    const Box::Interval& old_i{old_iv[i]};
    const Box::Interval& new_i{new_iv[i]};
    if (old_i != new_i) {
      os << variables[i] << " : " << old_i << " -> " << new_i << "\n";
    }
  }
  return os;
}

}  // namespace dreal
