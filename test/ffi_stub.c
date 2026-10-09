#include <caml/mlvalues.h>
/* opaque counter handle: the OCaml value itself is the handle */
value lg_counter_new(value v) { return v; }
value lg_counter_read(value v) { return v; }
