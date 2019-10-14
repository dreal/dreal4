#pragma once

namespace dreal {
template <typename... Args>
void unused(const Args&... /* unused */) {}
}  // namespace dreal

#ifdef NDEBUG
// To suppress unused variables warnings.
#define DREAL_ASSERT(x) unused(x);
#else
#include <assert.h>  // NOLINT
#define DREAL_ASSERT(x) assert(x)
#endif
