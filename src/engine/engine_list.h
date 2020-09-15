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

//
// ADD ALL THE ENGINES HERE
//

#include "engine/bmc/bmc_engine_info.h"
#include "engine/kind/kind_engine_info.h"
#include "engine/pdkind/pdkind_engine_info.h"
#include "engine/simulator/simulator_info.h"
#include "engine/translator/translator_info.h"

sally::engine_data::engine_data() {
  add_module_info<simulator::simulator_info>();
  add_module_info<bmc::bmc_engine_info>();
  add_module_info<kind::kind_engine_info>();
  add_module_info<pdkind::pdkind_engine_info>();
  add_module_info<output::translator_info>();
}

