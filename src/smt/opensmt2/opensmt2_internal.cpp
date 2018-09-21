//
// Created by Martin Blicha on 17.09.18.
//

#ifdef WITH_OPENSMT2

#include "opensmt2_internal.h"

#endif // WITH_OPENSMT2

namespace{
    template<typename C, typename E>
    bool contains(const C& container, const E& element) {
      return std::find(container.begin(), container.end(), element) != container.end();
    }
}

sally::smt::opensmt2_internal::opensmt2_internal(sally::expr::term_manager & tm, const sally::options & opts) :
    d_tm{tm}
    , term_cache{}
{
    auto logic_str = opts.get_string("solver-logic");
    if (logic_str == "QF-LRA" || logic_str == "QF_LRA") {
        osmt = new Opensmt(qf_lra, "osmt_solver");
        const char* msg;
        bool res = osmt->getConfig().setOption(":time-queries", SMTOption{0}, msg);
        assert(res);
        assert(strcmp(msg, "ok") == 0);
        res = osmt->getConfig().setOption(":verbosity", SMTOption{2}, msg);
        assert(strcmp(msg, "ok") == 0);
    }
}

void sally::smt::opensmt2_internal::add(sally::expr::term_ref ref, sally::smt::solver::formula_class f_class) {
    PTRef ptref = sally_to_osmt(ref);
    char** msg = nullptr;
    get_main_solver().insertFormula(ptref, msg);
}

sally::smt::solver::result sally::smt::opensmt2_internal::check() {
    auto res = get_main_solver().check();
    if (res == s_True) { return solver::SAT; }
    if (res == s_False) { return solver::UNSAT; }
    return solver::UNKNOWN;
}

void sally::smt::opensmt2_internal::push() {
    get_main_solver().push();
}

void sally::smt::opensmt2_internal::pop() {
    bool res = get_main_solver().pop();
    assert(res);
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
            break;
        case expr::CONST_BOOL:
            result = d_tm.get_boolean_constant(t) ? get_logic().getTerm_true() : get_logic().getTerm_false();
            break;
        case expr::CONST_RATIONAL: {
            std::stringstream ss;
            d_tm.get_rational_constant(t).to_stream(ss);
            result = get_lralogic().mkConst(ss.str().c_str());
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

PTRef sally::smt::opensmt2_internal::mk_osmt_term(sally::expr::term_op op, size_t n, std::vector<PTRef> children) {
    assert(n == children.size());
    auto & logic = get_logic();
    switch(op){
        case expr::TERM_ITE:
            assert(n == 3);
            return get_logic().mkIte(children[0], children[1], children[2]);
        case expr::TERM_EQ:
            assert(n == 2);
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
            assert(n == 2);
            return get_lralogic().mkNumMinus(children[0], children[1]);
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
