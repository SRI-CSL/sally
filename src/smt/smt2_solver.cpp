/*
 * smt2_solver.cpp
 *
 *  Created on: Nov 25, 2014
 *      Author: dejan
 */

#include "smt/smt2_solver.h"

#include <boost/iostreams/stream.hpp>
#include <boost/iostreams/device/file_descriptor.hpp>
#include <boost/iostreams/tee.hpp>

#include <fstream>
#include <iostream>

namespace sal2 {
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
class smt2_solver_internal {

  /** Term manager */
  expr::term_manager& d_tm;

  /** Stream where the solver responces can be read off */
  fd_read_stream* d_solver_response;

  /** Stream where we send all the solver input */
  fd_write_stream_tee* d_solver_input;

public:

  /**
   * Create the files and fork the solver.
   */
  smt2_solver_internal(expr::term_manager& tm)
  : d_tm(tm)
  , d_solver_response(0)
  , d_solver_input(0)
  {
    // Fork the solver

    // Setup the streams
  }

  ~smt2_solver_internal() {
    // Delete the streams you own
  }

  void add(expr::term_ref f) {
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
    return solver::UNKNOWN;
  }

  void push() {
    *d_solver_input << "(push 1)" << std::endl;
  }

  void pop() {
    *d_solver_input << "(pop 1)" << std::endl;
  }
};

smt2_solver::smt2_solver(expr::term_manager& tm)
: solver(tm, "generic smt2 solver")
{
  d_internal = new smt2_solver_internal(tm);
}

smt2_solver::~smt2_solver() {
  delete d_internal;
}

void smt2_solver::add(expr::term_ref f) {
  d_internal->add(f);
}

solver::result smt2_solver::check() {
  return d_internal->check();
}

void smt2_solver::push() {
  d_internal->push();
}

void smt2_solver::pop() {
  d_internal->pop();
}

}
}
