#include "dreal/solver/config.h"

#include <fmt/format.h>

namespace dreal {

using std::ostream;

double Config::precision() const { return precision_.get(); }
OptionValue<double>& Config::mutable_precision() { return precision_; }

bool Config::produce_models() const { return produce_models_.get(); }
OptionValue<bool>& Config::mutable_produce_models() { return produce_models_; }

bool Config::use_polytope() const { return use_polytope_.get(); }
OptionValue<bool>& Config::mutable_use_polytope() { return use_polytope_; }

bool Config::use_polytope_in_forall() const {
  return use_polytope_in_forall_.get();
}
OptionValue<bool>& Config::mutable_use_polytope_in_forall() {
  return use_polytope_in_forall_;
}

bool Config::use_worklist_fixpoint() const {
  return use_worklist_fixpoint_.get();
}
OptionValue<bool>& Config::mutable_use_worklist_fixpoint() {
  return use_worklist_fixpoint_;
}

bool Config::use_local_optimization() const {
  return use_local_optimization_.get();
}
OptionValue<bool>& Config::mutable_use_local_optimization() {
  return use_local_optimization_;
}

ostream& operator<<(ostream& os, const Config& config) {
  return os << fmt::format(
             "Config("
             "precision = {}, "
             "produce_model = {}, "
             "use_polytope = {}, "
             "use_polytope_in_forall = {}"
             "use_worklist_fixpoint = {}"
             "use_local_optimization = {}"
             ")",
             config.precision(), config.produce_models(), config.use_polytope(),
             config.use_polytope_in_forall(), config.use_worklist_fixpoint(),
             config.use_local_optimization());
}

}  // namespace dreal
