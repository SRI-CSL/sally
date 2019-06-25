/**
 * This file is part of sally.
 * Copyright (C) 2015 SRI International.
 *
 * Sally is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Sally is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with sally.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifdef WITH_DREAL

#include "smt/dreal/dreal_term.h"
#include "utils/exception.h"
#include "utils/hash.h"
#include "dreal/symbolic/prefix_printer.h"

using namespace dreal;

namespace sally {
namespace smt {

dreal_term::dreal_term()
  : d_type(dreal_term::type_t::NULL_TERM)
{}

dreal_term::dreal_term(std::string name, Variable::Type type) {
  if (type == Variable::Type::BOOLEAN) {
    d_type = dreal_term::type_t::FORMULA;
    d_f = Formula(Variable(name, type)); 
  } else {
    assert (type == Variable::Type::INTEGER || type == Variable::Type::CONTINUOUS);
    d_type = dreal_term::type_t::EXPRESSION;
    d_e = Expression(Variable(name, type));
  }
}

dreal_term::dreal_term(bool b)
  : d_type(dreal_term::type_t::FORMULA)
  , d_f(b ? Formula::True(): Formula::False())
{}

dreal_term::dreal_term(double v)
  : d_type(dreal_term::type_t::EXPRESSION)
  , d_e(Expression(v))
{}
  
dreal_term::dreal_term(Expression e)
  : d_type(dreal_term::type_t::EXPRESSION)
  , d_e(e)
{}

dreal_term::dreal_term(Formula f)
  : d_type(dreal_term::type_t::FORMULA)
  , d_f(f)
{}


dreal_term::type_t dreal_term::get_type() const {
  return d_type;
}

bool dreal_term::is_null_term() const {
  return d_type == dreal_term::type_t::NULL_TERM;
}

bool dreal_term::is_variable() const {
  switch(d_type) {
  case type_t::NULL_TERM: return false;
  case type_t::EXPRESSION: return ::is_variable(d_e);
  default: return ::is_variable(d_f);
  }
}

bool dreal_term::is_expression() const {
  return d_type == dreal_term::type_t::EXPRESSION;  
}

bool dreal_term::is_expression_variable() const {
  // integer or real variable
  return is_expression() && is_variable();  
}
  
bool dreal_term::is_formula() const {
  return d_type == dreal_term::type_t::FORMULA;    
}

bool dreal_term::is_formula_variable() const {
  // boolean variable
  return is_formula() && is_variable();  
}
  
const Expression& dreal_term::expression() const {
  if (get_type() != dreal_term::type_t::EXPRESSION) {
    throw exception("Dreal error (this term is not an expression)");      
  }
  return d_e;
}

const Formula& dreal_term::formula() const {
  if (get_type() != dreal_term::type_t::FORMULA) {
    throw exception("Dreal error (this term is not a formula)");      
  }
  return d_f;
}

const Variable& dreal_term::variable() const {
  if (is_formula_variable()) {
    return get_variable(d_f);
  } else if (is_expression_variable()) {
    return get_variable(d_e);
  } else {
    throw exception("Dreal error (this term is not a variable)");          
  }
}
  
bool dreal_term::operator==(const dreal_term& o) const {
  bool res = false;  
  if (d_type == o.d_type) {
    switch(d_type) {
    case type_t::NULL_TERM:
      res = true;
      break;
    case type_t::EXPRESSION:
      res = d_e.EqualTo(o.d_e);
      break;
    case type_t::FORMULA:
      res =  d_f.EqualTo(o.d_f);
      break;
    default:
      throw exception("Dreal error (unsupported type in dreal_term::operator==)");
    }
  }
  return res;
}

std::string dreal_term::to_string() const {
  switch(d_type) {
  case type_t::NULL_TERM: return "NULL TERM";
  case type_t::EXPRESSION: return d_e.to_string();
  default: return d_f.to_string();
  }
}

std::string dreal_term::to_smtlib2() const {
  if (is_formula()) {
    return ToPrefix(d_f);
  } else if (is_expression()) {
    return ToPrefix(d_e);
  } else {
    std::stringstream ss;
    ss << "Dreal error (cannot convert term " << to_string() << " to smt2 output)";
    throw exception(ss.str());      
  } 
}
  
size_t dreal_term::get_hash() const {
  // utils::sequence_hash hash;
  // hash.add(d_type);
  // hash.add(d_e.get_hash());
  // hash.add(d_f.get_hash());
  // return hash.get();
    
  if (is_expression()) {
    return d_e.get_hash();
  } else if (is_formula()) {
    return d_f.get_hash();
  } else {
    std::stringstream ss;
    ss << "Dreal error (cannot hash null term)";
    throw exception(ss.str());      
  }
}

/*
  dreal allows and of all combinations of Formula and Variable.
  Both Formula and Expression can be a Variable.
 */
dreal_term dreal_term::dreal_and(dreal_term t1, dreal_term t2) {
  if (t1.is_formula() && t2.is_formula()) {
    return dreal_term(t1.formula() && t2.formula());
  } else {
    throw exception("Dreal error (cannot create and term)");    
  }
}

dreal_term dreal_term::dreal_or(dreal_term t1, dreal_term t2) {
  if (t1.is_formula() && t2.is_formula()) {
    return dreal_term(t1.formula() || t2.formula());
  } else {
    throw exception("Dreal error (cannot create or term)");    
  }
}

dreal_term dreal_term::dreal_and(const std::vector<dreal_term>& children) {
  dreal_term res(Formula::True()); // this will be simplified by dreal
  for(unsigned i=0, e=children.size(); i<e; ++i) {
    res = dreal_and(res, children[i]);
  }
  return res;
}

  
dreal_term dreal_term::dreal_or(const std::vector<dreal_term>& children) {
  dreal_term res(Formula::False()); // this will be simplified by dreal
  for(unsigned i=0, e=children.size(); i<e; ++i) {
    res = dreal_or(res, children[i]);
  }
  return res;
}
  

dreal_term dreal_term::dreal_not(dreal_term t) {
  if (t.is_formula()) {
    return dreal_term(!t.formula());
  } else {
    throw exception("Dreal error (cannot create not term)");
  }
}

dreal_term dreal_term::dreal_eq(dreal_term t1, dreal_term t2){
  if (t1.is_expression() && t2.is_expression()) {
    return dreal_term(t1.expression() == t2.expression()); 
  } else if (t1.is_formula() && t2.is_formula()) {
    return dreal_term(t1.formula() == t2.formula());
  } else {
    throw exception("Dreal error (cannot create equal operator)");              
  }
}
  
dreal_term dreal_term::dreal_not_eq(dreal_term t1, dreal_term t2) {
  return dreal_not(dreal_eq(t1, t2));
}
  
dreal_term dreal_term::dreal_lt(dreal_term e1, dreal_term e2) {
  if (e1.is_expression() && e2.is_expression()) {
    return dreal_term(e1.expression() < e2.expression());
  } else {
    throw exception("Dreal error (cannot create < operator)");          
  }
}
  
dreal_term dreal_term::dreal_leq(dreal_term e1, dreal_term e2) {
  if (e1.is_expression() && e2.is_expression()) {
    return dreal_term(e1.expression() <= e2.expression());
  } else {
    throw exception("Dreal error (cannot create <= operator)");          
  }
}
  
dreal_term dreal_term::dreal_gt(dreal_term e1, dreal_term e2) {
  if (e1.is_expression() && e2.is_expression()) {
    return dreal_term(e1.expression() > e2.expression());
  } else {
    throw exception("Dreal error (cannot create > operator)");          
  }
}
  
dreal_term dreal_term::dreal_geq(dreal_term e1, dreal_term e2) {
  if (e1.is_expression() && e2.is_expression()) {
    return dreal_term(e1.expression() >= e2.expression());
  } else {
    throw exception("Dreal error (cannot create >= operator)");          
  }
}

dreal_term dreal_term::dreal_add(dreal_term e1, dreal_term e2) {
  if (e1.is_expression() && e2.is_expression()) {
    return dreal_term(e1.expression() + e2.expression());
  } else {
    throw exception("Dreal error (cannot create + operator)");          
  }
}

dreal_term dreal_term::dreal_add(const std::vector<dreal_term>& children) {
  dreal_term res(Expression::Zero()); // it will be simplified by dreal
  for (unsigned i=0, e=children.size(); i<e; ++i) {
    res = dreal_add(res, children[i]);
  }
  return res;
}
  
dreal_term dreal_term::dreal_sub(dreal_term e1, dreal_term e2) {
  if (e1.is_expression() && e2.is_expression()) {
    return dreal_term(e1.expression() - e2.expression());
  } else {
    throw exception("Dreal error (cannot create - operator)");          
  }
}

dreal_term dreal_term::dreal_sub(dreal_term e) {
  if (e.is_expression()) {
    return dreal_term(-e.expression());
  } else {
    throw exception("Dreal error (cannot create unary - operator)");          
  }
}
  
dreal_term dreal_term::dreal_mul(dreal_term e1, dreal_term e2) {
  if (e1.is_expression() && e2.is_expression()) {
    return dreal_term(e1.expression() * e2.expression());
  } else {
    throw exception("Dreal error (cannot create * operator)");          
  }
}

dreal_term dreal_term::dreal_mul(const std::vector<dreal_term>& children) {
  dreal_term res(Expression::One()); // it will be simplified by dreal
  for (unsigned i=0, e=children.size(); i<e; ++i) {
    res = dreal_mul(res, children[i]);
  }
  return res;
}
  
dreal_term dreal_term::dreal_div(dreal_term e1, dreal_term e2) {
  if (e1.is_expression() && e2.is_expression()) {
    return dreal_term(e1.expression() / e2.expression());
  } else {
    throw exception("Dreal error (cannot create / operator)");          
  }
}

dreal_term dreal_term::dreal_ite(dreal_term cond, dreal_term t1, dreal_term t2) {
  if (cond.is_formula() && t1.is_expression() && t2.is_expression()) {
    return dreal_term(if_then_else(cond.formula(), t1.expression(), t2.expression()));
  } else if (cond.is_formula() && t1.is_formula() && t2.is_formula()) {
    // the parser accepts ite with t1 and t2 being formula but
    // `if_then_else` only accepts expressions.
    return dreal_term(dreal_and(dreal_or(dreal_not(cond), t1),
				dreal_or(cond, t2)));
  } else {
    throw exception("Dreal error (cannot create ite operator)");
  }
}

std::ostream& operator<<(std::ostream& out, const dreal_term& t) {
  out << t.to_string();
  return out;
}
  
}
}
#endif   
