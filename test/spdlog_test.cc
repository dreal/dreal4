// From https://github.com/gabime/spdlog/wiki/1.-QuickStart
#include "spdlog/spdlog.h"
#include <iostream>
#include "spdlog/sinks/basic_file_sink.h"
#include "spdlog/sinks/rotating_file_sink.h"
#include "spdlog/sinks/stdout_color_sinks.h"

int main() {
  // Multithreaded console logger(with color support)
  auto console = spdlog::stdout_color_mt("console");
  console->info("Welcome to spdlog!");
  console->info("An info message example {}..", 1);

  try {
    // The following causes a heap-use-after-free in ASAN build. Disable it now.
    // Create basic file logger (not rotated)
    // auto my_logger = spdlog::basic_logger_mt("basic_logger",
    // "logs/basic.txt");

    // create a file rotating logger with 5mb size max and 3 rotated files
    auto file_logger = spdlog::rotating_logger_mt("file_logger", "myfilename",
                                                  1024 * 1024 * 5, 3);
  } catch (const spdlog::spdlog_ex& ex) {
    std::cout << "Log initialization failed: " << ex.what() << std::endl;
  }
}
