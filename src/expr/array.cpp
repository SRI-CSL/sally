#include "expr/array.h"
#include "expr/term.h"
#include "utils/output.h"

#include <iostream>
#include <cassert>

namespace sally {
namespace expr {

array_element::array_element(array_element::type_t t)
  : element_type(t) {
}

std::ostream& operator<<(std::ostream& out, const array_element& e) {
  e.write(out);
  return out;
}
  
/* array_element_b */
array_element_b::array_element_b(bool e)
  : array_element(array_element::ARRAY_BOOL)
  , element(e) {
}

bool array_element_b::operator==(const array_element& other) const {
  if (other.element_type == array_element::ARRAY_BOOL) {
    const array_element_b* other_b = static_cast<const array_element_b*>(&other);
    return element == other_b->element;
  }
  return false;
}

size_t array_element_b::hash() const {
  return element;
}

void array_element_b::write(std::ostream& out) const {
  out << element;
}
  
/* array_element_z */  
array_element_z::array_element_z(integer z)
  : array_element(array_element::ARRAY_INTEGER)
  , element(z) {
}

bool array_element_z::operator==(const array_element& other) const {
  if (other.element_type == array_element::ARRAY_INTEGER) {
    const array_element_z* other_z = static_cast<const array_element_z*>(&other);
    return element == other_z->element;
  }
  return false;
}

size_t array_element_z::hash() const {
  return element.hash();
}

void array_element_z::write(std::ostream& out) const {
  out << element;
}

/* array_element_q */  
array_element_q::array_element_q(rational q)
  : array_element(array_element::ARRAY_RATIONAL)
  , element(q) {
}

bool array_element_q::operator==(const array_element& other) const {
  if (other.element_type == array_element::ARRAY_RATIONAL) {
    const array_element_q* other_q = static_cast<const array_element_q*>(&other);
    return element == other_q->element;
  }
  return false;
}

size_t array_element_q::hash() const {
  return element.hash();
}

void array_element_q::write(std::ostream& out) const {
  out << element;
}

/* array_element_bv */  
array_element_bv::array_element_bv(bitvector bv)
  : array_element(array_element::ARRAY_BITVECTOR)
  , element(bv) {
}
  

bool array_element_bv::operator==(const array_element& other) const {
  if (other.element_type == array_element::ARRAY_BITVECTOR) {
    const array_element_bv* other_bv = static_cast<const array_element_bv*>(&other);
    return element == other_bv->element;
  }
  return false;
}

size_t array_element_bv::hash() const {
  return element.hash();
}

void array_element_bv::write(std::ostream& out) const {
  out << element;
}


/* array */  
array::array()
  : def_val() {}

array::array(array_element_ref def_val, const mapping_vector_t& _mappings)
  : def_val(def_val) {
  
  for (unsigned i=0, e=_mappings.size(); i<e; ++i) {
    assert(_mappings[i].size() >= 2);
    if (_mappings[i].size() >= 2) {
      // it must be at least x1 -> x2
      mappings.push_back(_mappings[i]);
    }
  }
}

bool array::operator==(const array& other) const {
  assert(def_val);
  assert(other.def_val);
  
  if (!def_val || !other.def_val) {
    return false;
  }
  
  if (!(*def_val == *other.def_val)) {
    return false;
  }
  if (mappings.size () != other.mappings.size()) {
    return false;
  }
  for (unsigned i=0, ie=mappings.size(); i<ie; ++i) {
    if (mappings[i].size() != other.mappings[i].size()) {
      return false;
    }
    for (unsigned j=0, je=mappings[i].size(); j<je; ++j) {
      if (*(mappings[i][j]) == *(other.mappings[i][j])) {
	return false;
      }
    }
  }
  return true;
}

size_t array::hash() const {
  assert(def_val);
  
  if (!def_val) {
    return 0;
  }

  utils::sequence_hash hasher;
  hasher.add(def_val->hash());
  for (unsigned i=0, ie=mappings.size(); i<ie; ++i) {
    const mapping_t &mapping = mappings[i];
    for (unsigned j=0, je=mapping.size(); j<je; ++j) {    
      hasher.add(mapping[j]->hash());
    }
  }
  return hasher.get();
}

void array::write(std::ostream& out) const {
  assert(def_val);
  if (!def_val) {
    out << "[]";
    return;
  }
  
  out << "[";
  for (unsigned i=0, ie=mappings.size(); i<ie; ++i) {
    const mapping_t &mapping = mappings[i];
    for (unsigned j=0, je=mapping.size()-1; j<je; ++j) {
      out << *(mapping[j]) << " ";
    }
    out << "-> " << *(mapping[mapping.size()-1]) << ",";
  }
  out << "else -> " << *def_val << "]";
}

array::array_element_ref array::mk_array_element_bool(int32_t v) {
  return array_element_ref(new array_element_b(v));
}
  
array::array_element_ref array::mk_array_element_z(mpz_t v) {
  return array_element_ref(new array_element_z(v));
}
  
array::array_element_ref array::mk_array_element_q(mpq_t v) {
  return array_element_ref(new array_element_q(v));
}
  
array::array_element_ref array::mk_array_element_bv(bitvector v) {
  return array_element_ref(new array_element_bv(v));
}

  
std::ostream& operator << (std::ostream& out, const array& a) {
  a.write(out);
  return out;
}
}
}
