#pragma once
#include <sys/stat.h>
#include <string>

namespace dreal {

/// Returns true if a filename @p name exists.
bool file_exists(const std::string& name);

}  // namespace dreal
