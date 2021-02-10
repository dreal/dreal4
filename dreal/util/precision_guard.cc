#include "dreal/util/precision_guard.h"

namespace dreal {

PrecisionGuard::PrecisionGuard(std::ostream* os,
                               const std::streamsize precision)
    : os_{os}, old_precision_(os->precision()) {
  os_->precision(precision);
}

PrecisionGuard::~PrecisionGuard() { os_->precision(old_precision_); }

}  // namespace dreal
