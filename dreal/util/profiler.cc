#include "dreal/util/profiler.h"

#include <utility>

using std::endl;
using std::move;
using std::ostream;
using std::string;

namespace dreal {
Profiler::Profiler(string name, ostream& out)
    : name_{move(name)},
      out_(out),
      begin_(std::chrono::high_resolution_clock::now()) {}

Profiler::~Profiler() {
  using duration = std::chrono::duration<double>;
  const auto diff = std::chrono::high_resolution_clock::now() - begin_;
  out_ << name_ << ": " << std::chrono::duration_cast<duration>(diff).count()
       << endl;
}

}  // namespace dreal
