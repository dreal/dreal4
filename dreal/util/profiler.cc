#include "dreal/util/profiler.h"

using std::endl;
using std::ostream;
using std::string;

namespace dreal {
Profiler::Profiler(const string& name, ostream& out)
    : name_(name),
      out_(out),
      begin_(std::chrono::high_resolution_clock::now()) {}

Profiler::~Profiler() {
  using duration = std::chrono::duration<double>;
  const auto diff = std::chrono::high_resolution_clock::now() - begin_;
  out_ << name_ << ": " << std::chrono::duration_cast<duration>(diff).count()
       << endl;
}

}  // namespace dreal
