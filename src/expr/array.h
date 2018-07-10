#pragma once

#include <iosfwd>
#include <vector>
#include "utils/hash.h"
#include "utils/smart_ptr.h"
#include "expr/integer.h"
#include "expr/rational.h"
#include "expr/bitvector.h"

namespace sally {
namespace expr {

/* Another wrapper for primitive types*/  
struct array_element {
  enum type_t { 
    ARRAY_BOOL,
    ARRAY_INTEGER,        
    ARRAY_RATIONAL,
    ARRAY_BITVECTOR
  };
  type_t element_type;
  array_element(type_t t);

  virtual ~array_element() {}
  virtual bool operator==(const array_element& other) const = 0;
  virtual size_t hash() const = 0;
  virtual void write(std::ostream& out) const = 0;
};

std::ostream& operator<<(std::ostream& out, const array_element& e);
  
class array_element_b: public array_element {
  bool element;
public:
  array_element_b(bool e);
  bool operator==(const array_element& other) const;
  size_t hash() const;
  void write(std::ostream& out) const;
};

class array_element_z: public array_element {
  integer element;
public:
  array_element_z(integer e);
  bool operator==(const array_element& other) const;
  size_t hash() const;
  void write(std::ostream& out) const;
};
  
class array_element_q: public array_element {
  rational element;
public:
  array_element_q(rational e);
  bool operator==(const array_element& other) const;
  size_t hash() const;
  void write(std::ostream& out) const;
};

class array_element_bv: public array_element {
  bitvector element;
public:
  array_element_bv(bitvector e);
  bool operator==(const array_element& other) const;
  size_t hash() const;
  void write(std::ostream& out) const;
};
  

/* 
   An array is a finite list of mappings and a default value. A
   mapping is of the form [x_1 ... x_k-1 -> x_k]. Each mapping
   specifies the value of an specific array element.
*/
class array {
public:
  typedef utils::smart_ptr<array_element> array_element_ref;
  typedef std::vector<array_element_ref> mapping_t;
  typedef std::vector<mapping_t> mapping_vector_t;
  
private:
  array_element_ref def_val;
  mapping_vector_t mappings;
    
public:
  static array_element_ref mk_array_element_bool(int32_t v);
  static array_element_ref mk_array_element_z(mpz_t v);
  static array_element_ref mk_array_element_q(mpq_t v);
  static array_element_ref mk_array_element_bv(bitvector v);
  
  array();
  array(array_element_ref def_val, const mapping_vector_t& mappings);
  bool operator==(const array& other) const;
  size_t hash() const;
  void write(std::ostream& out) const;
};

std::ostream& operator<<(std::ostream& out, const array& a);
}

namespace utils {

template<>
struct hash<expr::array> {
  size_t operator()(const expr::array& a) const {
    return a.hash();
  }
};

}
}
