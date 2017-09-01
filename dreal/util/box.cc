#include "dreal/util/box.h"

#include <algorithm>
#include <cmath>
#include <functional>
#include <limits>
#include <sstream>
#include <stdexcept>
#include <utility>

#include "dreal/util/logging.h"

using std::ceil;
using std::equal;
using std::find_if;
using std::floor;
using std::isfinite;
using std::make_pair;
using std::make_shared;
using std::move;
using std::numeric_limits;
using std::ostream;
using std::ostringstream;
using std::pair;
using std::runtime_error;
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

Box::Box(const Variables& variables)
    : variables_{make_shared<vector<Variable>>()},
      values_{static_cast<int>(variables.size())},
      var_to_idx_{
          make_shared<unordered_map<Variable, int, hash_value<Variable>>>()},
      idx_to_var_{make_shared<unordered_map<int, Variable>>()} {
  for (const Variable& var : variables) {
    Add(var);
  }
}

void Box::Add(const Variable v) {
  assert(find_if(variables_->begin(), variables_->end(),
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
}

void Box::Add(const Variable v, const double lb, const double ub) {
  assert(lb <= ub);
  Add(v);
  values_[(*var_to_idx_)[v]] = Interval{lb, ub};
}

bool Box::empty() const { return values_.is_empty(); }

void Box::set_empty() { values_.set_empty(); }

int Box::size() const { return variables_->size(); }

Box::Interval& Box::operator[](const int i) {
  assert(i < size());
  return values_[i];
}
Box::Interval& Box::operator[](const Variable& var) {
  return values_[(*var_to_idx_)[var]];
}
const Box::Interval& Box::operator[](const int i) const {
  assert(i < size());
  return values_[i];
}
const Box::Interval& Box::operator[](const Variable& var) const {
  return values_[(*var_to_idx_)[var]];
}

const vector<Variable>& Box::variables() const { return *variables_; }

const Variable& Box::variable(const int i) const { return (*idx_to_var_)[i]; }

int Box::index(const Variable& var) const { return (*var_to_idx_)[var]; }

const Box::IntervalVector& Box::interval_vector() const { return values_; }
Box::IntervalVector& Box::get_mutable_interval_vector() { return values_; }

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
    ostringstream oss;
    oss << "Variable " << var << " = " << values_[i]
        << " is not bisectable but Box::bisect is called.";
    throw runtime_error(oss.str());
  }
  switch (var.get_type()) {
    case Variable::Type::CONTINUOUS:
      return bisect_continuous(i);
    case Variable::Type::INTEGER:
      return bisect_int(i);
    case Variable::Type::BOOLEAN:
      throw runtime_error("Boolean variable is not supported in Box::Bisect.");
    case Variable::Type::BINARY:
      throw runtime_error("Binary variable is not supported in Box::Bisect.");
  }
  throw runtime_error("should not be reachable.");
}

pair<Box, Box> Box::bisect(const Variable& var) const {
  auto it = var_to_idx_->find(var);
  if (it != var_to_idx_->end()) {
    return bisect(it->second);
  } else {
    ostringstream oss;
    oss << "Variable " << var << " is not found in this box.";
    throw runtime_error(oss.str());
  }
  return bisect((*var_to_idx_)[var]);
}

pair<Box, Box> Box::bisect_int(const int i) const {
  assert(idx_to_var_->at(i).get_type() == Variable::Type::INTEGER);
  Box b1{*this};
  Box b2{*this};
  const Interval intv_i{values_[i]};
  double lb{intv_i.lb()};
  double ub{intv_i.ub()};
  lb = isfinite(lb) ? static_cast<int>(ceil(lb)) : -numeric_limits<int>::max();
  ub = isfinite(ub) ? static_cast<int>(floor(ub)) : numeric_limits<int>::max();
  const int mid{static_cast<int>(intv_i.mid())};
  b1[i] = Interval(lb, mid);
  b2[i] = Interval(mid + 1, ub);
  return make_pair(b1, b2);
}

pair<Box, Box> Box::bisect_continuous(const int i) const {
  assert(idx_to_var_->at(i).get_type() == Variable::Type::CONTINUOUS);
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
  assert(equal(variables().begin(), variables().end(), b.variables().begin(),
               b.variables().end(), std::equal_to<Variable>{}));
  values_ |= b.values_;
  return *this;
}

std::ostream& operator<<(std::ostream& os, const Box& box) {
  int i{0};
  for (const Variable& var : *(box.variables_)) {
    const Box::Interval interval{box.values_[i++]};
    os << var << " : " << interval;
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
