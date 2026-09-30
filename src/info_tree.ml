open Types

type entry_kind =
  | Expression
  | Pattern

type entry = {
  node_id : Source_node_id.t;
  location : Location.t;
  kind : entry_kind;
  name : string option;
  ty : ty option;
  resolved : string option;
}

let entries_ref : entry list ref Domain.DLS.key =
  Domain.DLS.new_key (fun () -> ref [])

let record entry =
  let entries = Domain.DLS.get entries_ref in
  entries := entry :: !entries

let record_pattern node_id location =
  record
    {
      node_id;
      location;
      kind = Pattern;
      name = None;
      ty = None;
      resolved = None;
    }

let reset () = Domain.DLS.get entries_ref := []

let snapshot () = List.rev !(Domain.DLS.get entries_ref)

let contains ~offset (location : Location.t) =
  (not location.loc_ghost)
  && location.loc_start.Lexing.pos_cnum <= offset
  && offset < location.loc_end.Lexing.pos_cnum

let span_size (location : Location.t) =
  location.loc_end.Lexing.pos_cnum - location.loc_start.Lexing.pos_cnum

let find ~offset entries =
  List.fold_left
    (fun best (entry : entry) ->
      if contains ~offset entry.location then
        match best with
        | None -> Some entry
        | Some current
          when span_size entry.location < span_size current.location ->
            Some entry
        | Some _ -> best
      else best)
    None entries
