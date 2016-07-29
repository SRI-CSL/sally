#include "sequence.h"

#include <iostream>

namespace sally {
namespace cmd {

sequence_command::sequence_command()
: command(SEQUENCE)
{}

sequence_command::~sequence_command() {
  for (size_t i = 0; i < d_commands.size(); ++ i) {
    delete d_commands[i];
  }
}

void sequence_command::push_back(command* command) {
  d_commands.push_back(command);
}

size_t sequence_command::size() const {
  return d_commands.size();
}

command* sequence_command::operator [] (size_t i) const {
  return d_commands[i];
}

void sequence_command::run(system::context* ctx, engine* e) {
  for (size_t i = 0; i < d_commands.size(); ++ i) {
    d_commands[i]->run(ctx, e);
  }
}

void sequence_command::to_stream(std::ostream& out) const {
  out << "[" << get_command_type_string();
  for (size_t i = 0; i < d_commands.size(); ++ i) {
    out << std::endl << *d_commands[i] << std::endl;
  }
  out << "]";
}

}
}
