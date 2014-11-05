grammar mcmt;

options {
  // C output for antlr
  language = 'C';
}

command returns [sal2::command* cmd = 0] 
  : 'declare-state-type' { $cmd = 0; }
  | 'define-states initial_states' { $cmd = 0; } 
  | 'define-transition' { $cmd = 0; } 
  | 'define-transition-system' { $cmd = 0; }  
  | 'query' { $cmd = 0; } 
  ;
  
/** Comments */
COMMENT
: ';' (~('\n' | '\r'))* { SKIP(); }
;