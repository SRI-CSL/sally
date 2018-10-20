//
// Created by Martin Blicha on 17.09.18.
//

#ifdef WITH_OPENSMT2

#include "opensmt2_internal.h"

#include <string>
#include <algorithm>

#include "expr/rational.h"
#include "utils/trace.h"

namespace{
    template<typename C, typename E>
    bool contains(const C& container, const E& element) {
      return std::find(container.begin(), container.end(), element) != container.end();
    }

    std::string rational_to_string(sally::expr::rational const & r){
      return r.mpq().get_str();
    }
}

unsigned int sally::smt::opensmt2_internal::instance_id = 0;

sally::smt::opensmt2_internal::opensmt2_internal(sally::expr::term_manager &tm, const sally::options &opts) :
    d_tm{tm}
    , d_instance{instance_id++}
    , term_cache{} {
  stacked_A_partitions.emplace_back();
  auto logic_str = opts.get_string("solver-logic");
  if (logic_str == "QF-LRA" || logic_str == "QF_LRA") {
    osmt = new Opensmt(qf_lra, "osmt_solver");
    const char *msg;
    bool res = osmt->getConfig().setOption(":time-queries", SMTOption{0}, msg);
    (void) res;
    assert(res);
    assert(strcmp(msg, "ok") == 0);
    osmt->getConfig().simplify_interpolant = 1;
//    osmt->getConfig().sat_theory_propagation = 0;
//    res = osmt->getConfig().setOption(":verbosity", SMTOption{2}, msg);
//    assert(strcmp(msg, "ok") == 0);
//    res = osmt->getConfig().setOption(":dump-query", SMTOption(1), msg);
//    res = osmt->getConfig().setOption(":dump-query-name", SMTOption("sally"), msg);


    const std::string itp_option = "opensmt2-itp";
    if (opts.has_option(itp_option)) {
      ItpAlgorithm itp {opts.get_int(itp_option)};
      osmt->getConfig().setLRAInterpolationAlgorithm(itp);
    }
  }
}

void sally::smt::opensmt2_internal::add(sally::expr::term_ref ref, sally::smt::solver::formula_class f_class) {

  TRACE("opensmt2") << "add: " << ref << std::endl;
  TRACE("opensmt2") << "class = " << f_class << std::endl;

  PTRef ptref = sally_to_osmt(ref);
    char** msg = nullptr;

    get_main_solver().insertFormula(ptref, msg);
//    std::cout << "Assigning partition " << current_partition << " to fla:\n" << get_logic().printTerm(ptref) << '\n';
    // A and T formula for A-part of interpolation problem; B formula form B-part
    if(f_class == sally::smt::solver::CLASS_A || f_class == sally::smt::solver::CLASS_T) {
      stacked_A_partitions[stack_level].push_back(current_partition);
    }
    ++current_partition;

}

sally::smt::solver::result sally::smt::opensmt2_internal::check() {
    auto res = get_main_solver().check();
//    std::cout << "Solver " << instance() << " got result: " << [res](){
//      if(res == s_True) return "SAT";
//      if(res == s_False) return "UNSAT";
//      return "UNKNOWN";
//    }() << '\n';
    if (res == s_True) { return solver::SAT; }
    if (res == s_False) { return solver::UNSAT; }
    return solver::UNKNOWN;
}

void sally::smt::opensmt2_internal::push() {
    get_main_solver().push();
    ++stack_level;
    stacked_A_partitions.emplace_back();
}

void sally::smt::opensmt2_internal::pop() {
  bool res = get_main_solver().pop();
  (void) res;
  assert(res);
  assert(stacked_A_partitions.size() == stack_level + 1); // we start at level 0
  --stack_level;
  assert(stack_level == 0); // TODO interpolation with incremental solving may not work properly
  stacked_A_partitions.pop_back();
}

PTRef sally::smt::opensmt2_internal::sally_to_osmt(sally::expr::term_ref ref) {
  PTRef result = term_cache.get_term_cache(ref);
  if (result != PTRef_Undef) { return result; }
    const expr::term& t = d_tm.term_of(ref);
    expr::term_op t_op = t.op();
    switch(t_op) {
        case expr::VARIABLE:
//            std::cout << t << std::endl;
            result = [this,&t]() {
                auto type = d_tm.term_of(t[0]).op();
//                std::cout << d_tm.term_of(t[0]) << std::endl;
                switch(type) {
                    case expr::TYPE_BOOL:
                        return get_logic().mkBoolVar(d_tm.get_variable_name(t).c_str());
                    case expr::TYPE_REAL:
                        return get_lralogic().mkNumVar(d_tm.get_variable_name(t).c_str());
                    default:
                        assert(false);
                }
                return PTRef_Undef;
            }();
            assert(result != PTRef_Undef);
            // for the variables we need to remember both ways of translation
            term_cache.set_osmt_term_cache(result, ref);
            break;
        case expr::CONST_BOOL:
            result = d_tm.get_boolean_constant(t) ? get_logic().getTerm_true() : get_logic().getTerm_false();
            break;
        case expr::CONST_RATIONAL: {
            std::string num = rational_to_string(d_tm.get_rational_constant(t));
            result = get_lralogic().mkConst(num.c_str());
            break;
        }
        case expr::TERM_ITE:
        case expr::TERM_EQ:
        case expr::TERM_AND:
        case expr::TERM_OR:
        case expr::TERM_NOT:
        case expr::TERM_IMPLIES:
        case expr::TERM_XOR:
        case expr::TERM_ADD:
        case expr::TERM_SUB:
        case expr::TERM_MUL:
        case expr::TERM_DIV:
        case expr::TERM_LEQ:
        case expr::TERM_LT:
        case expr::TERM_GEQ:
        case expr::TERM_GT:
        {
            size_t size = t.size();
            assert(size > 0);
            std::vector<PTRef> children;
            for (size_t i = 0; i < size; ++ i) {
                children.push_back(sally_to_osmt(t[i]));
            }
            result = mk_osmt_term(t.op(), size, children);
            break;
        }
        default:
            assert(false);
    }
    term_cache.set_term_cache(ref, result);
    return result;
}

PTRef sally::smt::opensmt2_internal::mk_osmt_term(sally::expr::term_op op, size_t n, const vector<PTRef> &children) {
    assert(n == children.size());
    auto & logic = get_logic();
    switch(op){
        case expr::TERM_ITE:
            assert(n == 3);
            return get_logic().mkIte(children[0], children[1], children[2]);
        case expr::TERM_EQ:
            assert(n == 2);
            if (get_lralogic().getSortRef(children[0]) == get_lralogic().getSort_num()){
              assert(get_lralogic().getSortRef(children[1]) == get_lralogic().getSort_num());
              return logic.mkAnd(
                get_lralogic().mkNumLeq(children[0], children[1]),
                get_lralogic().mkNumLeq(children[1], children[0])
                );
            }
            return logic.mkEq(children[0], children[1]);
        case expr::TERM_AND:
            return logic.mkAnd(children);
        case expr::TERM_OR:
            return logic.mkOr(children);
        case expr::TERM_NOT:
            assert(n == 1);
            return logic.mkNot(children[0]);
        case expr::TERM_IMPLIES:
            assert(n == 2);
            return logic.mkImpl(children[0], children[1]);
        case expr::TERM_XOR:
            assert(n ==2);
            return logic.mkXor(children[0], children[1]);
        case expr::TERM_ADD:
            return get_lralogic().mkNumPlus(children);
        case expr::TERM_SUB:
            assert(n == 2 || n == 1);
            return n == 1 ? (get_lralogic().mkNumNeg(children[0])) :
                  get_lralogic().mkNumMinus(children[0], children[1]);
        case expr::TERM_MUL:
            return get_lralogic().mkNumTimes(children);
        case expr::TERM_DIV:
            assert( n == 2);
            return get_lralogic().mkNumDiv(children[0], children[1]);
        case expr::TERM_LEQ:
            assert(n == 2);
            return get_lralogic().mkNumLeq(children[0], children[1]);
        case expr::TERM_LT:
            assert(n == 2);
            return get_lralogic().mkNumLt(children[0], children[1]);
        case expr::TERM_GEQ:
            assert(n == 2);
            return get_lralogic().mkNumGeq(children[0], children[1]);
        case expr::TERM_GT:
            assert(n == 2);
            return get_lralogic().mkNumGt(children[0], children[1]);
        default:
            assert(false);
    }
    return PTRef_Undef;
}

sally::expr::term_ref sally::smt::opensmt2_internal::osmt_to_sally(PTRef ref) {
  expr::term_ref result;

  // Check the cache
  result = term_cache.get_osmt_term_cache(ref);
  if (!result.is_null()) {
    return result;
  }

  auto &logic = get_logic();
  auto &lralogic = get_lralogic();
  if (logic.isTrue(ref)) {
    result = d_tm.mk_boolean_constant(true);
  } else if (logic.isFalse(ref)) {
    result = d_tm.mk_boolean_constant(false);
  } else if (lralogic.isConstant(ref)) {
    auto real = lralogic.getNumConst(ref);
    auto str_representation = real.get_str();
    mpq_t number;
    mpq_init(number);
    mpq_set_str(number, str_representation.c_str(), 10);
    expr::rational rational(number);
    result = d_tm.mk_rational_constant(rational);
    mpq_clear(number);
  } else if (logic.isAnd(ref)) {
    auto const &pterm = logic.getPterm(ref);
    std::vector<expr::term_ref> children;
    for (int i = 0; i < pterm.size(); ++i) {
      children.push_back(osmt_to_sally(pterm[i]));
    }
    result = d_tm.mk_and(children);
  } else if (logic.isOr(ref)) {
    auto const &pterm = logic.getPterm(ref);
    std::vector<expr::term_ref> children;
    for (int i = 0; i < pterm.size(); ++i) {
      children.push_back(osmt_to_sally(pterm[i]));
    }
    result = d_tm.mk_or(children);
  } else if (logic.isNot(ref)) {
    auto const &pterm = logic.getPterm(ref);
    assert(pterm.size() == 1);
    result = d_tm.mk_term(expr::TERM_NOT, osmt_to_sally(pterm[0]));
  } else if (logic.isIff(ref)) {
    assert(logic.getPterm(ref).size() == 2);
    auto const &child1 = logic.getPterm(ref)[0];
    auto const &child2 = logic.getPterm(ref)[1];
    result = d_tm.mk_term(expr::TERM_EQ, osmt_to_sally(child1), osmt_to_sally(child2));
  } else if (logic.isIte(ref)) {
    assert(logic.getPterm(ref).size() == 3);
    auto const &child1 = logic.getPterm(ref)[0];
    auto const &child2 = logic.getPterm(ref)[1];
    auto const &child3 = logic.getPterm(ref)[2];
    result = d_tm.mk_term(expr::TERM_ITE, osmt_to_sally(child1), osmt_to_sally(child2), osmt_to_sally(child3));
  } else if (lralogic.isEquality(ref)) {
    assert(logic.getPterm(ref).size() == 2);
    auto const &child1 = logic.getPterm(ref)[0];
    auto const &child2 = logic.getPterm(ref)[1];
    result = d_tm.mk_term(expr::TERM_EQ, osmt_to_sally(child1), osmt_to_sally(child2));
  } else if (lralogic.isNumLeq(ref)) {
    assert(logic.getPterm(ref).size() == 2);
    auto const &child1 = logic.getPterm(ref)[0];
    auto const &child2 = logic.getPterm(ref)[1];
    result = d_tm.mk_term(expr::TERM_LEQ, osmt_to_sally(child1), osmt_to_sally(child2));
  } else if (lralogic.isNumPlus(ref)) {
    auto const &pterm = logic.getPterm(ref);
    std::vector<expr::term_ref> children;
    for (int i = 0; i < pterm.size(); ++i) {
      children.push_back(osmt_to_sally(pterm[i]));
    }
    result = d_tm.mk_term(expr::TERM_ADD, children);
  } else if (lralogic.isNumTimes(ref)) {
    auto const &pterm = logic.getPterm(ref);
    std::vector<expr::term_ref> children;
    for (int i = 0; i < pterm.size(); ++i) {
      children.push_back(osmt_to_sally(pterm[i]));
    }
    result = d_tm.mk_term(expr::TERM_MUL, children);
  } else { assert(false); }

  // At this point we need to be non-null
  if (result.is_null()) {
    throw exception("OpenSMT error (term creation)");
  }

  // Set the cache ref -> result
  term_cache.set_osmt_term_cache(ref, result);

  return result;
}

sally::expr::model::ref sally::smt::opensmt2_internal::get_model() {
    // Create new model
    expr::model::ref m = new expr::model(d_tm, false);

    // Get the model from mathsat
    for (size_t i = 0; i < d_variables.size(); ++ i) {
        expr::term_ref var = d_variables[i];
        expr::term_ref var_type = d_tm.type_of(var);
        expr::value var_value;

        PTRef m_var = sally_to_osmt(var);
        const char* val = get_main_solver().getValue(m_var).val;

        switch (d_tm.term_of(var_type).op()) {
            case expr::TYPE_BOOL: {
              assert(strcmp(val, "true") == 0 || strcmp(val, "false") == 0);
              var_value = expr::value(strcmp(val, "true") == 0);
                break;
            }
            case expr::TYPE_INTEGER: {
                throw "Not implemented yet";
                break;
            }
            case expr::TYPE_REAL: {
                mpq_t value;
                mpq_init(value);
                mpq_set_str(value, val, 10);
                var_value = expr::value(expr::rational(value));
                mpq_clear(value);
                break;
            }
            case expr::TYPE_BITVECTOR: {
                throw "Opensmt does not support bit-vectors";
                break;
            }
            default:
                assert(false);
        }

        // Add the association
        m->set_variable_value(var, var_value);
    }
    return m;
}

void
sally::smt::opensmt2_internal::add_variable(sally::expr::term_ref var, sally::smt::solver::variable_class f_class) {
  assert(!contains(d_variables, var));
  d_variables.push_back(var);

}

void sally::smt::opensmt2_internal::generalize(sally::smt::solver::generalization_type type,
                                               const set<sally::expr::term_ref> &vars_to_keep,
                                               const set<sally::expr::term_ref> &vars_to_elim,
                                               expr::model::ref m,
                                               vector<sally::expr::term_ref> &out) {
  std::set<expr::term_ref>::const_iterator it = vars_to_keep.begin(), it_end = vars_to_keep.end();
  for (; it != it_end; ++it) {
    // var = value
    expr::term_ref var = *it;
    assert(m->has_value(var));
    expr::term_ref value = m->get_term_value(var).to_term(d_tm);

    if (d_tm.type_of(var) == d_tm.boolean_type()) {
      if (d_tm.get_boolean_constant(d_tm.term_of(value))) {
        out.push_back(var);
      } else {
        out.push_back(d_tm.mk_term(expr::TERM_NOT, var));
      }
    } else {
      out.push_back(d_tm.mk_term(expr::TERM_EQ, var, value));
    }
  }

}

void sally::smt::opensmt2_internal::interpolate(vector<sally::expr::term_ref> &out) {
  assert(get_main_solver().getStatus() == s_False);
  std::vector<PTRef> itps;
  auto & smt_solver = get_main_solver().getSMTSolver();
  auto A_mask = get_A_mask();
  smt_solver.createProofGraph();
//  std::cout << "Interpolation mask is: " << A_mask.get_str() << '\n';
  get_main_solver().getSMTSolver().getSingleInterpolant(itps, A_mask);
  assert(itps.size() == 1);
  smt_solver.deleteProofGraph();
  PTRef itp = itps[0];
//  std::cout << get_logic().printTerm(itp) << std::endl;
  out.push_back(osmt_to_sally(itp));
}

ipartitions_t sally::smt::opensmt2_internal::get_A_mask() const {
  ipartitions_t A_mask = 0;
  for (auto const & stack_level_partitions : stacked_A_partitions) {
    for (auto const & partition_idx : stack_level_partitions){
      setbit(A_mask, partition_idx);
    }
  }
  return A_mask;
}

#endif // WITH_OPENSMT2
