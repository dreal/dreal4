#include "dreal/util/interrupt.h"

namespace dreal {
volatile std::atomic_bool g_interrupted{false};
}  // namespace dreal
