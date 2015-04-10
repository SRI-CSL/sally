/*
 * term_map.h
 *
 *  Created on: Apr 10, 2015
 *      Author: dejan
 */

#pragma once

#include "expr/term.h"

#include <map>
#include <boost/unordered_map.hpp>
#include <functional>

namespace sally {
namespace expr {

/** Map from terms to values */
template <typename value>
class term_ref_map : public std::map<term_ref, value> {};

/** Map from terms to values */
template <typename value>
class term_ref_hash_map : public boost::unordered_map<expr::term_ref, value, expr::term_ref_hasher> {};

/** Map from keys to terms */
template <typename key, typename key_hasher, typename key_eq = std::equal_to<key> >
class hash_map_to_term_ref : public boost::unordered_map<key, expr::term_ref, key_hasher, key_eq> {};

}
}
