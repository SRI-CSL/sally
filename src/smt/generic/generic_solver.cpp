/*
 * smt2_solver.cpp
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#include "expr/term_manager.h"
#include "expr/gc_relocator.h"
#include "smt/generic/generic_solver.h"

#include <boost/iostreams/stream.hpp>
#include <boost/iostreams/device/file_descriptor.hpp>
#include <boost/iostreams/tee.hpp>

#include <fstream>
#include <iostream>
#include <sstream>

#include <unistd.h>

namespace sally {
namespace smt {

// FD-based stream for writing
typedef boost::iostreams::stream<boost::iostreams::file_descriptor_sink> fd_write_stream;
// FD-based stream for reading
typedef boost::iostreams::stream<boost::iostreams::file_descriptor_source> fd_read_stream;
// Tee for getting a copy of the input
typedef boost::iostreams::tee_device<fd_write_stream, std::ofstream> tee_device;
typedef boost::iostreams::stream<tee_device> fd_write_stream_tee;

/**
 * Internal class that does all the work.
 */
class generic_solver_internal {

  /** Term manager */
  expr::term_manager& d_tm;

  /** Stream where the solver responces can be read off */
  fd_read_stream* d_solver_response;

  /** Stream where we send the solver input */
  fd_write_stream* d_solver_input_fd;

  /** The tee device */
  tee_device* d_solver_input_tee_device;

  /** Wrapper so that we can split the output */
  std::ostream* d_solver_input_tee;

  /** Stream of the output file */
  std::ofstream* d_copy_out;

  /** Stream where we send the solver input */
  std::ostream* d_solver_input;

  /** List of declared variables */
  std::vector<expr::term_ref> d_vars_list;

  /** Set of declared variables */
  std::set<expr::term_ref> d_vars_set;

  /** Number of declared variables per push */
  std::vector<size_t> d_vars_list_size;

  /** Returns true if a variable is already declared */
  bool is_declared(expr::term_ref var) const {
    return d_vars_set.find(var) != d_vars_set.end();
  }

  /** Declares a variable to the solver */
  void declare(expr::term_ref var) {
    // Declare in the solver
    *d_solver_input << "(declare-fun " << var << " () " << d_tm.type_of(var) << ")" << std::endl;
    // Add to the list/set of declared variables
    d_vars_list.push_back(var);
    d_vars_set.insert(var);
  }

  /** Number of solver instances */
  static unsigned s_instances;

  /** The options */
  const options& d_options;

public:

  /**
   * Create the files and fork the solver.
   */
  generic_solver_internal(expr::term_manager& tm, const options& opts)
  : d_tm(tm)
  , d_solver_response(0)
  , d_solver_input_fd(0)
  , d_solver_input_tee_device(0)
  , d_solver_input_tee(0)
  , d_copy_out(0)
  , d_solver_input(0)
  , d_options(opts)
  {
    // The solver to run
    if (!d_options.has_option("generic-solver-script")) {
      throw exception("Use the 'generic-solver-script' option to specify the solver.");
    }
    std::string solver_script = d_options.get_string("generic-solver-script");

    if (!d_options.has_option("generic-solver-logic")) {
      throw exception("Use the 'generic-solver-logic' option to specify the SMT2 logic to use.");
    }
    std::string solver_logic = d_options.get_string("generic-solver-logic");

    // Should we log the interaction
    bool solver_log_enabled = d_options.has_option("generic-solver-log");
    std::string solver_log;
    if (solver_log_enabled) {
      std::stringstream ss;
      ss << opts.get_string("generic-solver-log");
      ss << "." << s_instances << ".smt2";
      solver_log = ss.str();
    }

    // One more instance
    s_instances ++;

    // Create pipe for sal -> solver
    int sal_to_solver_fds[2]; // [0]: solver read, [1]: sal write
    if (pipe(sal_to_solver_fds) == -1) {
      throw exception("could not create solver");
    }
    // Create the pipe for solver -> sal
    int solver_to_sal_fds[2]; // [0]: sal read, [1]: solver write
    if (pipe(solver_to_sal_fds) == -1) {
      throw exception("could not create solver");
    }

    // Fork the solver
    pid_t pid = fork();
    if (pid == -1) {
      throw exception("could not create solver");
    }

    // Child, solver side, never exits the if
    if (pid == 0) {
      // Close unused pipe ends
      close(sal_to_solver_fds[1]);
      close(solver_to_sal_fds[0]);

      // Take stdin from sal
      dup2(sal_to_solver_fds[0], 0);
      // Put stdout to sal
      dup2(solver_to_sal_fds[1], 1);

      // Run the actual solver
      char* const args[3] = { strdup(solver_script.c_str()), 0 };
      execvp(solver_script.c_str(), args);
      // We're in child, on this error just exit
      std::cerr << "failed to execute " << solver_script << "." << std::endl;
      exit(1);
    }

    // Parent, sal side
    close(sal_to_solver_fds[0]);
    close(solver_to_sal_fds[1]);

    // Where we write SMT2 to the solver
    d_solver_input_fd = new fd_write_stream(sal_to_solver_fds[1], boost::iostreams::close_handle);

    if (solver_log_enabled) {
      // Where the SMT2 copy goes
      d_copy_out = new std::ofstream(solver_log.c_str());
      // Make the device to tee to
      d_solver_input_tee_device = new tee_device(*d_solver_input_fd, *d_copy_out);
      // Where we write to get the double output
      d_solver_input_tee = new fd_write_stream_tee(*d_solver_input_tee_device);
      // This is the one we use
      d_solver_input = d_solver_input_tee;
    } else {
      // We write to the solver directly
      d_solver_input = d_solver_input_fd;
    }

    // Where we read from
    d_solver_response = new fd_read_stream(solver_to_sal_fds[0], boost::iostreams::close_handle);

    // Setup the solver stream
    *d_solver_input << expr::set_tm(tm);
    *d_solver_input << expr::set_output_language(output::MCMT);

    // SMT2 preamble
    *d_solver_input << "(set-info :smt-lib-version 2.0)" << std::endl;
    *d_solver_input << "(set-logic " << solver_logic << ")" << std::endl;
  }

  ~generic_solver_internal() {
    // Notify the solver
    *d_solver_input << "(exit)" << std::endl;
    // Delete the streams you own
    delete d_solver_response;
    delete d_solver_input_tee;
    delete d_solver_input_tee_device;
    delete d_solver_input_fd;
    delete d_copy_out;
  }

  void add(expr::term_ref f) {
    // Declare any undeclared variables
    std::vector<expr::term_ref> vars;
    d_tm.get_variables(f, vars);
    for (unsigned i = 0; i < vars.size(); ++ i) {
      if (!is_declared(vars[i])) {
        declare(vars[i]);
      }
    }

    *d_solver_input << "(assert " << f << ")" << std::endl;
  }

  solver::result check() {
    *d_solver_input << "(check-sat)" << std::endl;
    std::string solver_out;
    *d_solver_response >> solver_out;
    if (solver_out == "sat") {
      return solver::SAT;
    }
    if (solver_out == "unsat") {
      return solver::UNSAT;
    }
    if (solver_out == "unknown") {
      return solver::UNKNOWN;
    }
    throw exception("unknown solver response: " + solver_out);
    return solver::UNKNOWN;
  }

  void push() {
    // Push the solver
    *d_solver_input << "(push 1)" << std::endl;
    // Remember the declared variables
    d_vars_list_size.push_back(d_vars_list.size());
  }

  void pop() {
    // Pop the solver
    *d_solver_input << "(pop 1)" << std::endl;
    // Forget all the variables declared since last push
    if (d_vars_list_size.size() == 0) {
      throw exception("Calls to push/pop don't match.");
    }
    size_t size = d_vars_list_size.back();
    d_vars_list_size.pop_back();
    while (d_vars_list.size() > size) {
      expr::term_ref var = d_vars_list.back();
      d_vars_list.pop_back();
      d_vars_set.erase(var);
    }
  }

  void gc_collect(const expr::gc_relocator& gc_reloc) {
    gc_reloc.reloc(d_vars_list);
    gc_reloc.reloc(d_vars_set);
  }

};

unsigned generic_solver_internal::s_instances = 0;

generic_solver::generic_solver(expr::term_manager& tm, const options& opts)
: solver("generic smt2 solver", tm, opts)
{
  d_internal = new generic_solver_internal(tm, opts);
}

generic_solver::~generic_solver() {
  delete d_internal;
}

void generic_solver::add(expr::term_ref f, formula_class f_class) {
  d_internal->add(f);
}

solver::result generic_solver::check() {
  return d_internal->check();
}

void generic_solver::push() {
  d_internal->push();
}

void generic_solver::pop() {
  d_internal->pop();
}

void generic_solver::gc_collect(const expr::gc_relocator& gc_reloc) {
  d_internal->gc_collect(gc_reloc);
}

}
}
