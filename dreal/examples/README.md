Examples
========

 - [sat_checker.cc](sat_checker.cc) : Shows how to construct a formula and check
   delta-satisfiability of it. To build and execute the example, run
   the following commands at the project root.

   ```bash
   bazel build //dreal/examples:sat_checker  # build
   ./bazel-bin/dreal/examples/sat_checker    # run
   ```

 - [check_lyapunov.cc](check_lyapunov.cc) : Shows how to verify a
   candidate lyapunov function for a given system.  To build and
   execute the example, run the following commands at the project
   root.

   ```bash
   bazel build //dreal/examples:check_lyapunov  # build
   ./bazel-bin/dreal/examples/check_lyapunov    # run
   ```

 - [synthesize_lyapunov.cc](synthesize_lyapunov.cc) : Shows how to
   synthesize a lyapunov function for a given system.  To build
   and execute the example, run the following commands at the project
   root.

   ```bash
   bazel build //dreal/examples:synthesize_lyapunov  # build
   ./bazel-bin/dreal/examples/synthesize_lyapunov    # run
   ```
