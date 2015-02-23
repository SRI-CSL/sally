/*
 * smt2_output_wrapper.cpp
 *
 *  Created on: Feb 23, 2015
 *      Author: dejan
 */

#include "smt/smt2_output_wrapper.h"
#include "utils/name_transformer.h"

namespace sally {
namespace smt {

class smt2_name_transformer : public utils::name_transformer {
public:
  std::string apply(std::string id) const {
    // *:: -> ""
    std::string::size_type find = id.find_first_of("::");
    if (find != std::string::npos) {
      find += 2;
      id = id.substr(find);
    }
    // Replace any bad characters
    std::replace(id.begin(), id.end(), '!', '_');
    std::replace(id.begin(), id.end(), '.', '_');
    return id;
  }
};

class set_name_transformer {
  expr::term_manager& d_tm;
  smt2_name_transformer d_transformer;
  const utils::name_transformer* d_old_transformer;
public:
  set_name_transformer(expr::term_manager& tm)
  : d_tm(tm)
  , d_old_transformer(tm.get_name_transformer())
  {
    d_tm.set_name_transformer(&d_transformer);
  }
  ~set_name_transformer() {
    d_tm.set_name_transformer(d_old_transformer);
  }
};

smt2_output_wrapper::smt2_output_wrapper(expr::term_manager& tm, const options& opts, solver* solver, std::string filename)
: smt::solver("smt2_wrapper[" + filename + "]", tm, opts)
, d_solver(solver)
, d_output(filename.c_str())
, d_total_assertions_count(0)
{
  set_name_transformer nt(d_tm);

  // Setup the stream
  output::set_output_language(d_output, output::MCMT);
  output::set_term_manager(d_output, &d_tm);

  // Models by default
  d_output << "(set-option :produce-models true)" << std::endl;

  // Unsat cores if supported
  if (solver->supports(solver::UNSAT_CORE)) {
    d_output << "(set-option :produce-unsat-cores true)" << std::endl;
  }

  // Interpolation if supported
  if (solver->supports(solver::INTERPOLATION)) {
    d_output << "(set-option :produce-interpolants true)" << std::endl;
  }

}

smt2_output_wrapper::~smt2_output_wrapper() {
  delete d_solver;
}

bool smt2_output_wrapper::supports(feature f) const {
  return d_solver->supports(f);
}

void smt2_output_wrapper::add(expr::term_ref f, formula_class f_class) {
  set_name_transformer nt(d_tm);

  assertion a(d_total_assertions_count ++, f, f_class);
  d_assertions.push_back(a);

  bool needs_annotation = d_solver->supports(solver::UNSAT_CORE) || d_solver->supports(solver::INTERPOLATION);

  d_output << "(assert ";
  if (needs_annotation) {
    d_output << "(! ";
  }
  d_output << f;
  if (d_solver->supports(solver::UNSAT_CORE)) {
    d_output << " :named a" << a.index;
  }
  if (d_solver->supports(solver::INTERPOLATION)) {
    d_output << " :interpolation-group g" << a.index;
  }
  if (needs_annotation) {
    d_output << ")";
  }
  d_output << ")" << std::endl;

  d_solver->add(f, f_class);
}

solver::result smt2_output_wrapper::check() {
  set_name_transformer nt(d_tm);

  d_output << "(check-sat)" << std::endl;

  return d_solver->check();
}

void smt2_output_wrapper::get_model(expr::model& m) const {
  set_name_transformer nt(d_tm);

  std::ofstream& out_nonconst = const_cast<smt2_output_wrapper*>(this)->d_output;
  out_nonconst << "(get-value (";
  std::set<expr::term_ref>::const_iterator it;
  bool space = false;
  for (it = d_x_variables.begin(); it != d_x_variables.end(); ++ it, space = true) {
    if (space) { out_nonconst << " "; }
    out_nonconst << *it << std::endl;
  }
  for (it = d_y_variables.begin(); it != d_y_variables.end(); ++ it, space = true) {
    if (space) { out_nonconst << " "; }
    out_nonconst << *it << std::endl;
  }
  out_nonconst << "))" << std::endl;

  d_solver->get_model(m);
}

void smt2_output_wrapper::push() {
  set_name_transformer nt(d_tm);

  d_output << "(push 1)" << std::endl;
  d_solver->push();

  d_assertions_size.push_back(d_assertions.size());
}

void smt2_output_wrapper::pop() {
  set_name_transformer nt(d_tm);

  d_output << "(pop 1)" << std::endl;
  d_solver->pop();

  size_t size = d_assertions_size.back();
  d_assertions_size.pop_back();
  while (d_assertions.size() > size) {
    d_assertions.pop_back();
  }
}

void smt2_output_wrapper::generalize(std::vector<expr::term_ref>& projection_out) {
  set_name_transformer nt(d_tm);

  d_solver->generalize(projection_out);
}

void smt2_output_wrapper::interpolate(std::vector<expr::term_ref>& out) {
  set_name_transformer nt(d_tm);

  d_output << "(get-interpolant (";

  bool space = false;
  for (size_t i = 0; i < d_assertions.size(); ++ i) {
    if (d_assertions[i].f_class != CLASS_B) {
      if (space) { d_output << " "; }
      d_output << "g" << d_assertions[i].index;
      space = true;
    }
  }

  d_output << "))" << std::endl;

  d_solver->interpolate(out);
}

void smt2_output_wrapper::get_unsat_core(std::vector<expr::term_ref>& out) {
  set_name_transformer nt(d_tm);

  d_output << "(get-unsat-core)" << std::endl;
  d_solver->get_unsat_core(out);
}

void smt2_output_wrapper::add_x_variable(expr::term_ref x_var) {
  set_name_transformer nt(d_tm);

  d_output << "(declare-fun " << x_var << " () " << d_tm.type_of(x_var) << ")" << std::endl;
  solver::add_x_variable(x_var);
  d_solver->add_x_variable(x_var);
}

void smt2_output_wrapper::add_y_variable(expr::term_ref y_var) {
  set_name_transformer nt(d_tm);

  d_output << "(declare-fun " << y_var << " () " << d_tm.type_of(y_var) << ")" << std::endl;
  solver::add_y_variable(y_var);
  d_solver->add_y_variable(y_var);
}

}
}
