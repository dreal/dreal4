#pragma once

#include "dreal/symbolic/symbolic.h"
#include "dreal/util/box.h"

namespace dreal {

enum class FilterAssertionResult {
  NotFiltered,
  FilteredWithChange,
  FilteredWithoutChange,
};

/// If the @p assertion can be applied into the @p box update @p box
/// and return true. Otherwise, return false while keeping @p box
/// intact.
FilterAssertionResult FilterAssertion(const Formula& assertion, Box* box);
}  // namespace dreal
