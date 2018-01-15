#pragma once

#include <sys/stat.h>

#include <string>

namespace dreal {

/// Returns true if a filename @p name exists.
bool file_exists(const std::string& name);

/// Extracts the extension from @p name.
///
/// @note It returns an empty string if there is no extension in @p name.
std::string get_extension(const std::string& name);

}  // namespace dreal
