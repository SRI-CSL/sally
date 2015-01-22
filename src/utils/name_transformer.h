/*
 * name_transformer.h
 *
 *  Created on: Jan 21, 2015
 *      Author: dejan
 */

#pragma once

#include <string>

namespace sal2 {
namespace utils {

/** Transforms string -> string */
class name_transformer {
public:
  virtual std::string apply(std::string name) const = 0;
  virtual ~name_transformer() {};
};

}
}
