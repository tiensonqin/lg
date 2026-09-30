module Protocol_map = Map.Make (Protocol_id)
module Method_map = Map.Make (Method_id)

module Method_lookup_key = struct
  type t = string list * string

  let rec compare_owner left right =
    match (left, right) with
    | [], [] -> 0
    | [], _ -> -1
    | _, [] -> 1
    | left_part :: left_rest, right_part :: right_rest -> (
        match String.compare left_part right_part with
        | 0 -> compare_owner left_rest right_rest
        | result -> result)

  let compare (left_owner, left_name) (right_owner, right_name) =
    match compare_owner left_owner right_owner with
    | 0 -> String.compare left_name right_name
    | result -> result
end

module Method_lookup_map = Map.Make (Method_lookup_key)

type method_signature = {
  method_id : Method_id.t;
  method_ty : Types.ty;
}

type declaration = {
  protocol_id : Protocol_id.t;
  location : Location.t option;
  methods : method_signature Method_map.t;
  method_locations : Location.t Method_map.t;
}

type receiver_id = Receiver_id.t =
  | Default_receiver
  | Int_receiver
  | Float_receiver
  | Char_receiver
  | String_receiver
  | Symbol_receiver
  | Keyword_receiver
  | Bool_receiver
  | Unit_receiver
  | Nil_receiver
  | List_receiver
  | Vector_receiver
  | Set_receiver
  | Seq_receiver
  | Array_receiver
  | Ref_receiver
  | Tuple_receiver
  | Host_receiver of string
  | Record_receiver of Type_id.t

module Implementation_key = struct
  type t = Protocol_id.t * Method_id.t * receiver_id

  let compare = Stdlib.compare
end

module Implementation_map = Map.Make (Implementation_key)
module Emitted_name_map = Map.Make (String)

module Marker_implementation_key = struct
  type t = Protocol_id.t * receiver_id

  let compare = Stdlib.compare
end

module Marker_implementation_set = Set.Make (Marker_implementation_key)

type t = {
  declarations : declaration Protocol_map.t;
  method_protocols : Protocol_id.t list Method_lookup_map.t;
  implementations : Types.binding Implementation_map.t;
  marker_implementations : Marker_implementation_set.t;
  implementation_locations : Location.t Implementation_map.t;
  implementation_names : Implementation_key.t Emitted_name_map.t;
}

let empty =
  {
    declarations = Protocol_map.empty;
    method_protocols = Method_lookup_map.empty;
    implementations = Implementation_map.empty;
    marker_implementations = Marker_implementation_set.empty;
    implementation_locations = Implementation_map.empty;
    implementation_names = Emitted_name_map.empty;
  }

let add_method_protocol protocol_id method_id method_protocols =
  let key = (Protocol_id.owner protocol_id, Method_id.name method_id) in
  let protocols =
    Method_lookup_map.find_opt key method_protocols
    |> Option.value ~default:[]
  in
  Method_lookup_map.add key
    (List.sort_uniq Protocol_id.compare (protocol_id :: protocols))
    method_protocols

let index_declarations declarations =
  Protocol_map.fold
    (fun protocol_id declaration method_protocols ->
      Method_map.fold
        (fun method_id _ method_protocols ->
          add_method_protocol protocol_id method_id method_protocols)
        declaration.methods method_protocols)
    declarations Method_lookup_map.empty

let declare ?location ?(method_locations = []) protocol_id signatures registry =
  if Protocol_map.mem protocol_id registry.declarations then
    Error.error ~code:Error_code.Duplicate
      ("duplicate protocol declaration " ^ Protocol_id.to_string protocol_id)
  else
    let rec methods acc = function
      | [] -> Ok acc
      | signature :: rest ->
          if Method_map.mem signature.method_id acc then
            Error.error ~code:Error_code.Duplicate
              ("duplicate protocol method "
             ^ Method_id.to_string signature.method_id)
          else methods (Method_map.add signature.method_id signature acc) rest
    in
    match methods Method_map.empty signatures with
    | Error _ as err -> err
    | Ok methods ->
        let method_locations =
          List.fold_left
            (fun locations (method_id, location) ->
              Method_map.add method_id location locations)
            Method_map.empty method_locations
        in
        let declaration =
          { protocol_id; location; methods; method_locations }
        in
        let method_protocols =
          Method_map.fold
            (fun method_id _ method_protocols ->
              add_method_protocol protocol_id method_id method_protocols)
            methods registry.method_protocols
        in
        Ok
          {
            registry with
            declarations =
              Protocol_map.add protocol_id declaration registry.declarations;
            method_protocols;
          }

let find_protocol protocol_id registry =
  Protocol_map.find_opt protocol_id registry.declarations

let find_method protocol_id method_id registry =
  match find_protocol protocol_id registry with
  | None -> None
  | Some declaration -> Method_map.find_opt method_id declaration.methods

let declarations registry = Protocol_map.bindings registry.declarations

let protocol_location protocol_id registry =
  Option.bind (find_protocol protocol_id registry) (fun declaration ->
      declaration.location)

let method_location protocol_id method_id registry =
  Option.bind (find_protocol protocol_id registry) (fun declaration ->
      Method_map.find_opt method_id declaration.method_locations)

let protocols_for_method ~owner ~method_name registry =
  Method_lookup_map.find_opt (owner, method_name) registry.method_protocols
  |> Option.value ~default:[]

let add_implementation ?location protocol_id method_id receiver_id binding
    registry =
  let key = (protocol_id, method_id, receiver_id) in
  if Implementation_map.mem key registry.implementations then
    Error.error ~code:Error_code.Duplicate
      ("duplicate protocol implementation "
      ^ Protocol_id.to_string protocol_id
     ^ "/" ^ Method_id.name method_id)
  else
    let add ~track_name =
      Ok
        {
          registry with
          implementations =
            Implementation_map.add key binding registry.implementations;
          implementation_locations =
            (match location with
            | Some location ->
                Implementation_map.add key location
                  registry.implementation_locations
            | None -> registry.implementation_locations);
          implementation_names =
            if track_name then
              Emitted_name_map.add binding.ocaml_name key
                registry.implementation_names
            else registry.implementation_names;
        }
    in
    match
      Emitted_name_map.find_opt binding.Types.ocaml_name
        registry.implementation_names
    with
    | Some (existing_protocol, existing_method, _existing_receiver)
      when Protocol_id.equal existing_protocol protocol_id
           && Method_id.equal existing_method method_id ->
        add ~track_name:false
    | Some (existing_protocol, existing_method, _existing_receiver) ->
        Error.error ~code:Error_code.Protocol
          ("OCaml protocol implementation name collision: "
          ^ Protocol_id.to_string existing_protocol
          ^ "/"
          ^ Method_id.name existing_method
          ^ " and "
          ^ Protocol_id.to_string protocol_id
          ^ "/" ^ Method_id.name method_id ^ " both emit " ^ binding.ocaml_name
          )
    | None -> add ~track_name:true

let find_implementation protocol_id method_id receiver_id registry =
  Implementation_map.find_opt
    (protocol_id, method_id, receiver_id)
    registry.implementations

let find_implementation_or_default protocol_id method_id receiver_id registry =
  match find_implementation protocol_id method_id receiver_id registry with
  | Some _ as implementation -> implementation
  | None ->
      find_implementation protocol_id method_id Default_receiver registry

let add_marker_implementation protocol_id receiver_id registry =
  {
    registry with
    marker_implementations =
      Marker_implementation_set.add (protocol_id, receiver_id)
        registry.marker_implementations;
  }

let has_marker_implementation protocol_id receiver_id registry =
  Marker_implementation_set.mem (protocol_id, receiver_id)
    registry.marker_implementations

let replace_implementation protocol_id method_id receiver_id binding registry =
  let key = (protocol_id, method_id, receiver_id) in
  if Implementation_map.mem key registry.implementations then
    {
      registry with
      implementations =
        Implementation_map.add key binding registry.implementations;
    }
  else registry

let implementations_for_method protocol_id method_id registry =
  Implementation_map.fold
    (fun (candidate_protocol, candidate_method, _) implementation matches ->
      if
        Protocol_id.equal protocol_id candidate_protocol
        && Method_id.equal method_id candidate_method
      then implementation :: matches
      else matches)
    registry.implementations []

let implementation_locations registry =
  Implementation_map.bindings registry.implementation_locations

let export_owner ~from_owner ~to_owner ~from_module ~to_module source target =
  let replace_prefix value =
    let prefix = from_module ^ "." in
    if String.starts_with ~prefix value then
      to_module
      ^ String.sub value
          (String.length from_module)
        (String.length value - String.length from_module)
    else value
  in
  let remap_owner owner =
    match (from_owner, to_owner, owner) with
    | [ from_path ], [ to_path ], [ owner_path ] ->
        if owner_path = from_path then Some [ to_path ]
        else
          let prefix = from_path ^ "." in
          if String.starts_with ~prefix owner_path then
            Some
              [
                to_path
                ^ String.sub owner_path (String.length from_path)
                    (String.length owner_path - String.length from_path);
              ]
          else None
    | _ when owner = from_owner -> Some to_owner
    | _ -> None
  in
  let remap_protocol protocol_id =
    match remap_owner (Protocol_id.owner protocol_id) with
    | Some owner ->
        Protocol_id.create ~owner ~name:(Protocol_id.name protocol_id)
    | None -> protocol_id
  in
  let remap_type_id type_id =
    match remap_owner (Type_id.owner type_id) with
    | Some owner -> Type_id.create ~owner ~name:(Type_id.name type_id)
    | None -> type_id
  in
  let remap_receiver = function
    | Record_receiver type_id -> Record_receiver (remap_type_id type_id)
    | receiver -> receiver
  in
  let remap_method protocol_id method_id =
    Method_id.create
      ~owner:(Protocol_id.owner protocol_id @ [ Protocol_id.name protocol_id ])
      ~name:(Method_id.name method_id)
  in
  let declarations =
    Protocol_map.fold
      (fun protocol_id declaration declarations ->
        match remap_owner (Protocol_id.owner protocol_id) with
        | None -> declarations
        | Some _ ->
          let protocol_id = remap_protocol protocol_id in
          let methods =
            Method_map.fold
              (fun _ signature methods ->
                  let method_id =
                    remap_method protocol_id signature.method_id
                  in
                Method_map.add method_id
                    {
                      method_id;
                      method_ty =
                        Types.remap_module_type ~from_path:from_module
                          ~to_path:to_module signature.method_ty;
                  }
                  methods)
              declaration.methods Method_map.empty
          in
          let method_locations =
            Method_map.fold
              (fun method_id location locations ->
                  Method_map.add
                    (remap_method protocol_id method_id)
                    location locations)
              declaration.method_locations Method_map.empty
          in
          Protocol_map.add protocol_id
              {
                protocol_id;
              location = declaration.location;
              methods;
                method_locations;
              }
            declarations)
      source.declarations target.declarations
  in
  let implementations =
    Implementation_map.fold
      (fun (protocol_id, method_id, receiver_id) binding implementations ->
        match remap_owner (Protocol_id.owner protocol_id) with
        | None -> implementations
        | Some _ ->
          let protocol_id = remap_protocol protocol_id in
          let method_id = remap_method protocol_id method_id in
          let receiver_id = remap_receiver receiver_id in
          let binding =
            {
              binding with
              Types.ocaml_name = replace_prefix binding.Types.ocaml_name;
              ty =
                Types.remap_module_type ~from_path:from_module
                  ~to_path:to_module binding.ty;
              protocol_id = Option.map remap_protocol binding.protocol_id;
            }
          in
            Implementation_map.add
              (protocol_id, method_id, receiver_id)
              binding implementations)
      source.implementations target.implementations
  in
  let marker_implementations =
    Marker_implementation_set.fold
      (fun (protocol_id, receiver_id) markers ->
        match remap_owner (Protocol_id.owner protocol_id) with
        | None -> markers
        | Some _ ->
            Marker_implementation_set.add
              (remap_protocol protocol_id, remap_receiver receiver_id)
              markers)
      source.marker_implementations target.marker_implementations
  in
  let implementation_locations =
    Implementation_map.fold
      (fun (protocol_id, method_id, receiver_id) location locations ->
        match remap_owner (Protocol_id.owner protocol_id) with
        | None -> locations
        | Some _ ->
            let protocol_id = remap_protocol protocol_id in
            let method_id = remap_method protocol_id method_id in
            Implementation_map.add
              (protocol_id, method_id, remap_receiver receiver_id)
              location locations)
      source.implementation_locations target.implementation_locations
  in
  let implementation_names =
    Implementation_map.fold
      (fun key binding names ->
        Emitted_name_map.add binding.Types.ocaml_name key names)
      implementations Emitted_name_map.empty
  in
  let method_protocols = index_declarations declarations in
  {
    declarations;
    method_protocols;
    implementations;
    marker_implementations;
    implementation_locations;
    implementation_names;
  }

let qualify_implementations ~owner ~module_name registry =
  let owner_prefix = Names.sanitize_name (String.concat "/" owner) ^ "_" in
  let implementations =
    Implementation_map.fold
      (fun (protocol_id, method_id, receiver_id) (binding : Types.binding)
           result ->
        if
          List.equal String.equal (Protocol_id.owner protocol_id) owner
          || String.starts_with ~prefix:owner_prefix binding.ocaml_name
        then
          let receiver_id =
            match receiver_id with
            | Record_receiver type_id -> Record_receiver type_id
            | receiver_id -> receiver_id
          in
          let binding =
            {
              binding with
              ocaml_name = module_name ^ "." ^ binding.ocaml_name;
              ty = Types.qualify_module_type module_name binding.ty;
            }
          in
          Implementation_map.add
            (protocol_id, method_id, receiver_id)
            binding result
        else
          Implementation_map.add
            (protocol_id, method_id, receiver_id)
            binding result)
      registry.implementations Implementation_map.empty
  in
  let implementation_names =
    Implementation_map.fold
      (fun key (binding : Types.binding) names ->
        Emitted_name_map.add binding.ocaml_name key names)
      implementations Emitted_name_map.empty
  in
  { registry with implementations; implementation_names }
