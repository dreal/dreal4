#include "dreal/util/filesystem.h"

namespace dreal {

using std::string;

bool file_exists(const string& name) {
  struct stat buffer;
  if (stat(name.c_str(), &buffer) != 0) {
    return false;
  }
  return S_ISREG(buffer.st_mode);
}
}  // namespace dreal
