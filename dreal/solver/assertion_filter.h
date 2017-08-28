#pragma once

#include "dreal/util/box.h"
#include "dreal/util/symbolic.h"

namespace dreal {

/// If the @p assertion can be applied into the @p box update @p box
/// and return true. Otherwise, return false while keeping @p box
/// intact.
bool FilterAssertion(const Formula& assertion, Box* box);
}  // namespace dreal
