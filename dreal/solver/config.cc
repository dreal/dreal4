#include "dreal/solver/config.h"

namespace dreal {
double Config::precision() const { return precision_; }
void Config::set_precision(const double precision) { precision_ = precision; }

bool Config::produce_models() const { return produce_models_; }
void Config::set_produce_models(const bool produce_models) {
  produce_models_ = produce_models;
}

bool Config::use_polytope() const { return use_polytope_; }
void Config::set_use_polytope(const bool value) { use_polytope_ = value; }

bool Config::use_polytope_in_forall() const { return use_polytope_in_forall_; }
void Config::set_use_polytope_in_forall(const bool value) {
  use_polytope_in_forall_ = value;
}

}  // namespace dreal
