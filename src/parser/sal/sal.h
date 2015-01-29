/*
 * sal_parser_traits.h
 *
 *  Created on: Dec 1, 2014
 *      Author: dejan
 */

#pragma once

#include "system/context.h"
#include "parser/antlr_parser.h"

namespace sally {
namespace parser {

antlr_parser_interface* new_sal_parser(const system::context& ctx, const char* filename);

}
}
