#include "dreal/solver/context.h"

#include <utility>

#include "dreal/solver/context_impl.h"
#include "dreal/util/exception.h"
#include "dreal/util/logging.h"
#include "dreal/version.h"

using std::make_unique;
using std::move;
using std::string;
using std::vector;

namespace dreal {

Context::Context() : Context{Config{}} {}

Context::Context(Context&& context) noexcept : impl_{move(context.impl_)} {}

Context::~Context() = default;

Context::Context(Config config) : impl_{make_unique<Impl>(config)} {}

void Context::Assert(const Formula& f) { impl_->Assert(f); }

optional<Box> Context::CheckSat() { return impl_->CheckSat(); }

void Context::DeclareVariable(const Variable& v, const bool is_model_variable) {
  impl_->DeclareVariable(v, is_model_variable);
}

void Context::DeclareVariable(const Variable& v, const Expression& lb,
                              const Expression& ub,
                              const bool is_model_variable) {
  impl_->DeclareVariable(v, is_model_variable);
  impl_->SetDomain(v, lb, ub);
}

void Context::Exit() { DREAL_LOG_DEBUG("Context::Exit()"); }

void Context::Minimize(const Expression& f) { impl_->Minimize({f}); }

void Context::Minimize(const vector<Expression>& functions) {
  impl_->Minimize(functions);
}

void Context::Maximize(const Expression& f) { impl_->Minimize({-f}); }

void Context::Pop(int n) {
  DREAL_LOG_DEBUG("Context::Pop({})", n);
  if (n <= 0) {
    throw DREAL_RUNTIME_ERROR(
        "Context::Pop(n) called with n = {} which is not positive.", n);
  }
  while (n-- > 0) {
    impl_->Pop();
  }
}

void Context::Push(int n) {
  DREAL_LOG_DEBUG("Context::Push({})", n);
  if (n <= 0) {
    throw DREAL_RUNTIME_ERROR(
        "Context::Push(n) called with n = {} which is not positive.", n);
  }
  while (n-- > 0) {
    impl_->Push();
  }
}

void Context::SetInfo(const string& key, const double val) {
  impl_->SetInfo(key, val);
}

void Context::SetInfo(const string& key, const string& val) {
  impl_->SetInfo(key, val);
}

void Context::SetInterval(const Variable& v, const double lb, const double ub) {
  impl_->SetInterval(v, lb, ub);
}

void Context::SetLogic(const Logic& logic) { impl_->SetLogic(logic); }

void Context::SetOption(const string& key, const double val) {
  impl_->SetOption(key, val);
}

void Context::SetOption(const string& key, const string& val) {
  impl_->SetOption(key, val);
}

const Config& Context::config() const { return impl_->config(); }
Config& Context::mutable_config() { return impl_->mutable_config(); }

string Context::version() { return DREAL_VERSION_STRING; }

const Box& Context::box() const { return impl_->box(); }

const Box& Context::get_model() const { return impl_->get_model(); }

const ScopedVector<Formula>& Context::assertions() const {
  return impl_->assertions();
}

}  // namespace dreal
