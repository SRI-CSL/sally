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

#pragma once

#ifdef WITH_DREAL

#include <dreal/dreal.h>

#include <vector>
#include <string>

/* 
   Dreal provides two classes Expression and Formula. It also provides
   a class Term that wraps these two classes together but the API is
   not sufficient for what we need (e.g., it doesn't allow to build
   new Term's from existing Term's, we cannot have null terms, etc).
 */
namespace sally {
namespace smt {

  class dreal_term {
  public:
    enum class type_t { NULL_TERM, EXPRESSION, FORMULA };

    /** Construct a null term */
    explicit dreal_term();

    /** Construct a variable */    
    explicit dreal_term(std::string name, ::dreal::Variable::Type type);

    /** Construct a constant boolean */        
    explicit dreal_term(bool b);

    /** Construct a constant double */            
    explicit dreal_term(double v);        
    
    /** Construct a term with e */
    explicit dreal_term(::dreal::Expression e);
    
    /** Construct a term with f */
    explicit dreal_term(::dreal::Formula f);
    
    /** Returns its type */
    type_t get_type() const;

    /** Return true if NULL_TERM */
    bool is_null_term() const;

    /** Return true if variable */
    bool is_variable() const;
    
    /** Return true if EXPRESSION */
    bool is_expression() const;

    /** Return true if variable and EXPRESSION */
    bool is_expression_variable() const;
    
    /** Return true if FORMULA */
    bool is_formula() const;

    /** Return true if variable and FORMULA */
    bool is_formula_variable() const;
    
    /** Returns the expression inside */
    const ::dreal::Expression& expression() const;
    
    /** Returns the formula inside */
    const ::dreal::Formula& formula() const;

    /** Returns the variable inside */
    const ::dreal::Variable& variable() const;
    
    /** Check structural equality */
    bool operator==(const dreal_term& o) const;

    /** Returns hash of term */
    size_t get_hash() const;
    
    /** Returns term as a string */
    std::string to_string() const;

    /** Convert to string the smtlib2 representation of the dreal term */
    std::string to_smtlib2() const;
    
    /** Return the conjunction of all terms */
    static dreal_term dreal_and(const std::vector<dreal_term>& children);
    static dreal_term dreal_and(dreal_term f1, dreal_term f2);    

    /** Return the disjunction of all terms */
    static dreal_term dreal_or(const std::vector<dreal_term>& children);
    static dreal_term dreal_or(dreal_term f1, dreal_term f2);        

    /** Return the negation of t */
    static dreal_term dreal_not(dreal_term t);

    /** Create an ite operator from cond, e1 and e2 */        
    static dreal_term dreal_ite(dreal_term cond, dreal_term e1, dreal_term e2);
    
    /** Create a relational operator from terms */
    static dreal_term dreal_eq(dreal_term e1, dreal_term e2);
    static dreal_term dreal_not_eq(dreal_term e1, dreal_term e2);
    static dreal_term dreal_lt(dreal_term e1, dreal_term e2);
    static dreal_term dreal_leq(dreal_term e1, dreal_term e2);
    static dreal_term dreal_gt(dreal_term e1, dreal_term e2);
    static dreal_term dreal_geq(dreal_term e1, dreal_term e2);

    /** Create an arithmetic operator from terms */    
    static dreal_term dreal_add(dreal_term e1, dreal_term e2);
    static dreal_term dreal_add(const std::vector<dreal_term>& children);    
    static dreal_term dreal_sub(dreal_term e1, dreal_term e2);
    static dreal_term dreal_sub(dreal_term e); //unary minus operator    
    static dreal_term dreal_mul(dreal_term e1, dreal_term e2);
    static dreal_term dreal_mul(const std::vector<dreal_term>& children);        
    static dreal_term dreal_div(dreal_term e1, dreal_term e2);

    /** TODO: dreal also supports operators such as log, abs, exp,
	sqrt, pow, sin, cos, tan, asin, acos, atan, atan2, sinh, cosh,
	tanh, min,max, Sum, and Prod. **/
    
  private:
    type_t d_type;
    ::dreal::Expression d_e;
    ::dreal::Formula d_f;
  };

  /** Dreal term hash. */
  struct dreal_hasher {
    size_t operator()(const dreal_term& t) const { return t.get_hash(); }    
  };

  std::ostream& operator<<(std::ostream& out, const dreal_term& t);
  
}
}
#endif   
