(*
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Pyre
module ParameterVariable = Type.Variable.Variadic.Parameters
module UnaryVariable = Type.Variable.Unary
module ListVariadic = Type.Variable.Variadic.List

type unary_interval = {
  upper_bound: Type.t;
  lower_bound: Type.t;
}
[@@deriving show]

type callable_parameter_interval =
  | Top
  | Singleton of Type.Callable.parameters
  | Bottom
[@@deriving show]

(* This approach of making which bounds actually exist explicit allows us to avoid making artificial
   Top and Bottom members of (Type.t Type.OrderedTypes.t) *)
type list_variadic_interval =
  | NoBounds
  | OnlyUpperBound of Type.OrderedTypes.t
  | OnlyLowerBound of Type.OrderedTypes.t
  | BothBounds of {
      upper: Type.OrderedTypes.t;
      lower: Type.OrderedTypes.t;
    }
[@@deriving show]

module Record = struct
  module VariadicTupleConstraints = struct
    type variadic_constraint_pair = {
      left_elements: Type.t list;
      right_elements: Type.t list;
    }
    [@@deriving show, compare]

    (* Going with a simple list of pairs for now. We can optimize this to be a map from Ts to the
       constraints containing it. *)
    type t = variadic_constraint_pair list [@@deriving show, compare]

    let empty = []
  end
end

type t = {
  unaries: unary_interval UnaryVariable.Map.t;
  variadic_tuple_constraints: Record.VariadicTupleConstraints.t;
  callable_parameters: callable_parameter_interval ParameterVariable.Map.t;
  list_variadics: list_variadic_interval ListVariadic.Map.t;
  have_fallbacks: Type.Variable.Set.t;
}

let show_map map ~show_key ~show_data ~short_name =
  if Map.is_empty map then
    ""
  else
    let show ~key ~data sofar =
      Printf.sprintf "%s => %s" (show_key key) (show_data data) :: sofar
    in
    Map.fold map ~init:[] ~f:show |> String.concat ~sep:"\n" |> Format.sprintf "%s: [%s]" short_name


let pp
    format
    { unaries; variadic_tuple_constraints; callable_parameters; list_variadics; have_fallbacks }
  =
  let unaries =
    show_map unaries ~show_key:UnaryVariable.show ~show_data:show_unary_interval ~short_name:"un"
  in
  let callable_parameters =
    show_map
      callable_parameters
      ~show_key:ParameterVariable.show
      ~show_data:show_callable_parameter_interval
      ~short_name:"cb"
  in
  let list_variadics =
    show_map
      list_variadics
      ~show_key:ListVariadic.show
      ~show_data:show_list_variadic_interval
      ~short_name:"lv"
  in
  let have_fallbacks =
    Set.to_list have_fallbacks
    |> List.to_string ~f:Type.Variable.show
    |> Format.sprintf "\nHave Fallbacks to Any: %s"
  in
  Format.fprintf
    format
    "{%s\n%s\n%s%s%s}"
    unaries
    ([%show: Record.VariadicTupleConstraints.t] variadic_tuple_constraints)
    callable_parameters
    list_variadics
    have_fallbacks


let show annotation = Format.asprintf "%a" pp annotation

let empty =
  {
    unaries = UnaryVariable.Map.empty;
    variadic_tuple_constraints = Record.VariadicTupleConstraints.empty;
    callable_parameters = ParameterVariable.Map.empty;
    list_variadics = ListVariadic.Map.empty;
    have_fallbacks = Type.Variable.Set.empty;
  }


let exists_in_bounds { unaries; callable_parameters; list_variadics; _ } ~variables =
  let contains_variable annotation =
    let contains_unary =
      Type.Variable.GlobalTransforms.Unary.collect_all annotation
      |> List.exists ~f:(fun variable ->
             List.mem variables (Type.Variable.Unary variable) ~equal:Type.Variable.equal)
    in
    let contains_parameter_variadic =
      let parameter_variadic_contained_in_list variable =
        List.mem variables (Type.Variable.ParameterVariadic variable) ~equal:Type.Variable.equal
      in
      Type.Variable.GlobalTransforms.ParameterVariadic.collect_all annotation
      |> List.exists ~f:parameter_variadic_contained_in_list
    in
    let contains_list_variadic =
      let list_variadic_contained_in_list variable =
        List.mem variables (Type.Variable.ListVariadic variable) ~equal:Type.Variable.equal
      in
      Type.Variable.GlobalTransforms.ListVariadic.collect_all annotation
      |> List.exists ~f:list_variadic_contained_in_list
    in
    contains_unary || contains_parameter_variadic || contains_list_variadic
  in
  let exists_in_interval_bounds { upper_bound; lower_bound } =
    contains_variable upper_bound || contains_variable lower_bound
  in
  let exists_in_callable_parameter_interval_bounds = function
    | Singleton parameters ->
        Type.Callable.create ~parameters ~annotation:Type.Any () |> contains_variable
    | _ -> false
  in
  let exists_in_list_variadic_interval_bounds interval =
    let exists = function
      | Type.OrderedTypes.Concrete types -> List.exists types ~f:contains_variable
      | Concatenation concatenation ->
          let contains = List.exists ~f:contains_variable in
          let in_head () = Type.OrderedTypes.Concatenation.head concatenation |> contains in
          let in_middle () =
            Type.OrderedTypes.Concatenation.variable concatenation
            |> (fun variable -> Type.Variable.ListVariadic variable)
            |> List.mem variables ~equal:Type.Variable.equal
          in
          let in_tail () = Type.OrderedTypes.Concatenation.tail concatenation |> contains in
          in_head () || in_middle () || in_tail ()
      | _ -> false
    in
    match interval with
    | NoBounds -> false
    | OnlyLowerBound bound
    | OnlyUpperBound bound ->
        exists bound
    | BothBounds { upper; lower } -> exists upper || exists lower
  in
  UnaryVariable.Map.exists unaries ~f:exists_in_interval_bounds
  || ParameterVariable.Map.exists
       callable_parameters
       ~f:exists_in_callable_parameter_interval_bounds
  || ListVariadic.Map.exists list_variadics ~f:exists_in_list_variadic_interval_bounds


module Solution = struct
  type t = {
    unaries: Type.t UnaryVariable.Map.t;
    callable_parameters: Type.Callable.parameters ParameterVariable.Map.t;
    list_variadics: Type.OrderedTypes.t ListVariadic.Map.t;
  }

  let equal left right =
    UnaryVariable.Map.equal Type.equal left.unaries right.unaries
    && ParameterVariable.Map.equal
         Type.Callable.equal_parameters
         left.callable_parameters
         right.callable_parameters
    && ListVariadic.Map.equal Type.OrderedTypes.equal left.list_variadics right.list_variadics


  let show { unaries; callable_parameters; list_variadics } =
    let unaries =
      show_map unaries ~show_key:UnaryVariable.show ~show_data:Type.show ~short_name:"un"
    in
    let callable_parameters =
      show_map
        callable_parameters
        ~show_key:ParameterVariable.show
        ~show_data:Type.Callable.show_parameters
        ~short_name:"cb"
    in
    let list_variadics =
      show_map
        list_variadics
        ~show_key:ListVariadic.show
        ~show_data:Type.OrderedTypes.show
        ~short_name:"lv"
    in
    Format.sprintf "{%s%s%s}" unaries callable_parameters list_variadics


  let empty =
    {
      unaries = UnaryVariable.Map.empty;
      callable_parameters = ParameterVariable.Map.empty;
      list_variadics = ListVariadic.Map.empty;
    }


  let instantiate { unaries; callable_parameters; list_variadics } annotation =
    let annotation =
      if UnaryVariable.Map.is_empty unaries then
        annotation
      else
        Type.Variable.GlobalTransforms.Unary.replace_all
          (fun variable -> UnaryVariable.Map.find unaries variable)
          annotation
    in
    let annotation =
      if ParameterVariable.Map.is_empty callable_parameters then
        annotation
      else
        Type.Variable.GlobalTransforms.ParameterVariadic.replace_all
          (fun variable -> ParameterVariable.Map.find callable_parameters variable)
          annotation
    in
    let annotation =
      if ListVariadic.Map.is_empty list_variadics then
        annotation
      else
        Type.Variable.GlobalTransforms.ListVariadic.replace_all
          (fun variable -> ListVariadic.Map.find list_variadics variable)
          annotation
    in
    annotation


  let instantiate_single_variable { unaries; _ } = UnaryVariable.Map.find unaries

  let instantiate_single_list_variadic_variable { list_variadics; _ } =
    ListVariadic.Map.find list_variadics


  let instantiate_single_parameter_variadic { callable_parameters; _ } =
    ParameterVariable.Map.find callable_parameters


  let instantiate_ordered_types solution = function
    | Type.OrderedTypes.Concrete concretes ->
        List.map concretes ~f:(instantiate solution)
        |> fun concretes -> Type.OrderedTypes.Concrete concretes
    | Any -> Any
    | Concatenation concatenation ->
        let mapped =
          Type.OrderedTypes.Concatenation.map_head_and_tail concatenation ~f:(instantiate solution)
        in
        let replacement = instantiate_single_list_variadic_variable solution in
        Type.OrderedTypes.Concatenation.replace_variable mapped ~replacement
        |> Option.value ~default:(Type.OrderedTypes.Concatenation mapped)


  let instantiate_callable_parameters solution parameters =
    match instantiate solution (Type.Callable.create ~parameters ~annotation:Type.Any ()) with
    | Type.Callable { implementation = { parameters; _ }; _ } -> parameters
    | _ -> failwith "instantiate is not preserving callables"


  let set ({ unaries; callable_parameters; list_variadics } as solution) = function
    | Type.Variable.UnaryPair (key, data) ->
        { solution with unaries = UnaryVariable.Map.set unaries ~key ~data }
    | Type.Variable.ParameterVariadicPair (key, data) ->
        {
          solution with
          callable_parameters = ParameterVariable.Map.set callable_parameters ~key ~data;
        }
    | Type.Variable.ListVariadicPair (key, data) ->
        { solution with list_variadics = ListVariadic.Map.set list_variadics ~key ~data }


  let create = List.fold ~f:set ~init:empty
end

module type OrderedConstraintsType = sig
  type order

  val add_lower_bound : t -> order:order -> pair:Type.Variable.pair -> t option

  val add_upper_bound : t -> order:order -> pair:Type.Variable.pair -> t option

  val add_variadic_tuple_constraint
    :  t ->
    order:order ->
    left_elements:Type.t list ->
    right_elements:Type.t list ->
    t option

  val add_fallback_to_any : t -> Type.Variable.t -> t

  val solve : t -> order:order -> Solution.t option

  val extract_partial_solution
    :  t ->
    order:order ->
    variables:Type.Variable.t list ->
    (t * Solution.t) option
end

module type OrderType = sig
  type t

  val always_less_or_equal : t -> left:Type.t -> right:Type.t -> bool

  val meet : t -> Type.t -> Type.t -> Type.t

  val join : t -> Type.t -> Type.t -> Type.t
end

module OrderedConstraints (Order : OrderType) = struct
  module IntervalContainer = struct
    module type Interval = sig
      module Variable : Type.Variable.VariableKind

      type t

      val create : ?upper_bound:Variable.domain -> ?lower_bound:Variable.domain -> unit -> t

      val intersection : t -> t -> order:Order.t -> t option

      (* Returns the lowest non-bottom value within the interval, such that it fulfills the
         requirements potentially given in the variable *)
      val narrowest_valid_value
        :  t ->
        order:Order.t ->
        variable:Variable.t ->
        Variable.domain option

      val merge_solution_in : t -> variable:Variable.t -> solution:Solution.t -> t

      val is_trivial : t -> variable:Variable.t -> bool

      val free_variables : t -> Type.Variable.t list
    end

    module Make (Interval : Interval) = struct
      let add_bound container ~order ~variable ~bound ~is_lower_bound =
        if Interval.Variable.equal_domain bound (Interval.Variable.self_reference variable) then
          Some container
        else
          let new_constraint =
            if is_lower_bound then
              Interval.create ~lower_bound:bound ()
            else
              Interval.create ~upper_bound:bound ()
          in
          let existing =
            Map.find container variable |> Option.value ~default:(Interval.create ())
          in
          Interval.intersection existing new_constraint ~order
          >>= fun intersection ->
          Interval.narrowest_valid_value intersection ~order ~variable
          >>| fun _ -> Map.set container ~key:variable ~data:intersection


      let merge_solution container ~solution =
        Map.mapi container ~f:(fun ~key ~data ->
            Interval.merge_solution_in data ~variable:key ~solution)
        |> Map.filteri ~f:(fun ~key ~data -> not (Interval.is_trivial data ~variable:key))


      let partition_independent_dependent container ~with_regards_to =
        let contains_key { unaries; callable_parameters; list_variadics; have_fallbacks; _ } key =
          let has_constraints =
            match key with
            | Type.Variable.Unary unary -> Map.mem unaries unary
            | Type.Variable.ParameterVariadic parameters -> Map.mem callable_parameters parameters
            | Type.Variable.ListVariadic variable -> Map.mem list_variadics variable
          in
          has_constraints || Set.mem have_fallbacks key
        in
        let is_independent target =
          Interval.free_variables target |> List.exists ~f:(contains_key with_regards_to) |> not
        in
        Map.partition_tf container ~f:is_independent


      let add_solution container partial_solution ~order =
        let add_solution ~key:variable ~data:target = function
          | Some partial_solution ->
              Interval.narrowest_valid_value target ~order ~variable
              >>| (fun value -> Interval.Variable.pair variable value)
              >>| Solution.set partial_solution
          | None -> None
        in
        Map.fold container ~f:add_solution ~init:(Some partial_solution)
    end
  end

  module UnaryTypeInterval = struct
    module Variable = UnaryVariable

    type t = unary_interval

    let lower_bound { lower_bound; _ } = lower_bound

    let upper_bound { upper_bound; _ } = upper_bound

    let create ?(upper_bound = Type.Top) ?(lower_bound = Type.Bottom) () =
      { upper_bound; lower_bound }


    let intersection left right ~order =
      Some
        {
          upper_bound = Order.meet order left.upper_bound right.upper_bound;
          lower_bound = Order.join order left.lower_bound right.lower_bound;
        }


    let narrowest_valid_value
        interval
        ~order
        ~variable:{ UnaryVariable.constraints = exogenous_constraint; _ }
      =
      let lowest_non_bottom_member interval ~order =
        let non_empty { upper_bound; lower_bound } ~order =
          Order.always_less_or_equal order ~left:lower_bound ~right:upper_bound
        in
        Option.some_if (non_empty interval ~order) (lower_bound interval)
        >>| function
        | Type.Bottom -> upper_bound interval
        | other -> other
      in
      match exogenous_constraint with
      | Explicit explicits ->
          let collect annotation sofar =
            let add_to_explicits_if_safe sofar candidate =
              match candidate with
              | { Type.Variable.Unary.constraints = Explicit left_constraints; _ } as candidate ->
                  let exists_in_explicits left_constraint =
                    List.exists explicits ~f:(Type.equal left_constraint)
                  in
                  if List.for_all left_constraints ~f:exists_in_explicits then
                    (* The only other thing that an explicit type variable can instantiate to is
                       another type variable with a subset of its values *)
                    Type.Variable candidate :: sofar
                  else
                    sofar
              | _ -> sofar
            in
            Type.Variable.GlobalTransforms.Unary.collect_all annotation
            |> List.fold ~f:add_to_explicits_if_safe ~init:sofar
          in
          let explicits =
            collect (lower_bound interval) explicits |> collect (upper_bound interval)
          in
          let contains { upper_bound; lower_bound } candidate ~order =
            Order.always_less_or_equal order ~left:candidate ~right:upper_bound
            && Order.always_less_or_equal order ~left:lower_bound ~right:candidate
          in
          (* When doing multiple solves, all of these options ought to be considered, *)
          (* and solved in a fixpoint *)
          List.find ~f:(contains interval ~order) explicits
      | Bound exogenous_bound ->
          intersection interval (create ~upper_bound:exogenous_bound ()) ~order
          >>= lowest_non_bottom_member ~order
      | Unconstrained -> lowest_non_bottom_member interval ~order
      | LiteralIntegers -> (
          let is_literal_integer = function
            | Type.Literal (Type.Integer _) -> true
            | Variable { constraints = LiteralIntegers; _ } -> true
            | _ -> false
          in
          let member = lowest_non_bottom_member interval ~order in
          match member with
          | Some found_member when is_literal_integer found_member -> member
          | Some (Type.Union union) when List.for_all union ~f:is_literal_integer -> member
          | _ -> None )


    let merge_solution_in { upper_bound; lower_bound } ~variable ~solution =
      let smart_instantiate annotation =
        let instantiated = Solution.instantiate solution annotation in
        Option.some_if (not (Type.equal instantiated (Type.Variable variable))) instantiated
      in
      let upper_bound = smart_instantiate upper_bound in
      let lower_bound = smart_instantiate lower_bound in
      create ?upper_bound ?lower_bound ()


    let is_trivial interval ~variable:_ =
      match interval with
      | { upper_bound = Type.Top; lower_bound = Type.Bottom } -> true
      | _ -> false


    let free_variables { upper_bound; lower_bound } =
      Type.Variable.all_free_variables upper_bound @ Type.Variable.all_free_variables lower_bound
  end

  module CallableParametersInterval = struct
    module Variable = ParameterVariable

    type t = callable_parameter_interval

    let create ?upper_bound ?lower_bound () =
      match upper_bound, lower_bound with
      | None, None -> Bottom
      | Some only, None
      | None, Some only ->
          Singleton only
      | Some left, Some right when Type.Callable.equal_parameters left right -> Singleton left
      | Some _, Some _ -> Top


    let narrowest_valid_value interval ~order:_ ~variable:_ =
      match interval with
      | Top
      | Bottom ->
          None
      | Singleton parameters -> Some parameters


    let intersection left right ~order:_ =
      match left, right with
      | Top, _
      | _, Top ->
          Some Top
      | other, Bottom
      | Bottom, other ->
          Some other
      | Singleton left, Singleton right when Type.Callable.equal_parameters left right ->
          Some (Singleton left)
      | _, _ -> Some Top


    let merge_solution_in target ~variable:_ ~solution =
      match target with
      | Top
      | Bottom ->
          target
      | Singleton parameters -> (
          let callable = Type.Callable.create ~parameters ~annotation:Type.Any () in
          match Solution.instantiate solution callable with
          | Type.Callable { implementation = { parameters = instantiated_parameters; _ }; _ } ->
              Singleton instantiated_parameters
          | _ -> failwith "impossible" )


    let is_trivial interval ~variable =
      match interval with
      | Singleton
          (Type.Callable.ParameterVariadicTypeVariable { head = []; variable = target_variable }) ->
          ParameterVariable.equal variable target_variable
      | _ -> false


    let free_variables = function
      | Top
      | Bottom ->
          []
      | Singleton parameters ->
          Type.Callable.create ~parameters ~annotation:Type.Any ()
          |> Type.Variable.all_free_variables
  end

  module ListVariadicInterval = struct
    module Variable = ListVariadic

    type t = list_variadic_interval

    let create ?upper_bound ?lower_bound () =
      match upper_bound, lower_bound with
      | None, None -> NoBounds
      | Some upper, None -> OnlyUpperBound upper
      | None, Some lower -> OnlyLowerBound lower
      | Some upper, Some lower -> BothBounds { upper; lower }


    let less_or_equal order ~left ~right =
      if Type.OrderedTypes.equal left right then
        true
      else
        match left, right with
        | _, Any
        | Any, _ ->
            true
        | Concatenation _, _
        | _, Concatenation _ ->
            false
        | Concrete upper_bounds, Concrete lower_bounds -> (
            match List.zip upper_bounds lower_bounds with
            | Ok bounds ->
                List.for_all bounds ~f:(fun (left, right) ->
                    Order.always_less_or_equal order ~left ~right)
            | _ -> false )


    let narrowest_valid_value interval ~order ~variable:_ =
      match interval with
      | NoBounds -> None
      | OnlyLowerBound bound
      | OnlyUpperBound bound ->
          Some bound
      | BothBounds { upper; lower } ->
          Option.some_if (less_or_equal order ~left:lower ~right:upper) lower


    let intersection left right ~order =
      let meet left right =
        if Type.OrderedTypes.equal left right then
          Some left
        else if less_or_equal order ~left ~right then
          Some left
        else if less_or_equal order ~left:right ~right:left then
          Some right
        else
          match left, right with
          | Concrete left, Concrete right -> (
              match List.zip left right with
              | Ok zipped ->
                  List.map zipped ~f:(fun (left, right) -> Order.meet order left right)
                  |> fun concrete_list -> Some (Type.OrderedTypes.Concrete concrete_list)
              | _ -> None )
          | _ -> None
      in
      let join left right =
        if Type.OrderedTypes.equal left right then
          Some left
        else if less_or_equal order ~left ~right then
          Some right
        else if less_or_equal order ~left:right ~right:left then
          Some left
        else
          match left, right with
          | Concrete left, Concrete right -> (
              match List.zip left right with
              | Ok zipped ->
                  List.map zipped ~f:(fun (left, right) -> Order.join order left right)
                  |> fun concrete_list -> Some (Type.OrderedTypes.Concrete concrete_list)
              | _ -> None )
          | _ -> None
      in
      match left, right with
      | NoBounds, other
      | other, NoBounds ->
          Some other
      | OnlyLowerBound lower, OnlyUpperBound upper
      | OnlyUpperBound upper, OnlyLowerBound lower ->
          Some (BothBounds { lower; upper })
      | OnlyLowerBound left, OnlyLowerBound right ->
          join left right >>| fun lower -> OnlyLowerBound lower
      | OnlyUpperBound left, OnlyUpperBound right ->
          meet left right >>| fun upper -> OnlyUpperBound upper
      | OnlyUpperBound upper, BothBounds both
      | BothBounds both, OnlyUpperBound upper ->
          meet upper both.upper >>| fun upper -> BothBounds { both with upper }
      | OnlyLowerBound lower, BothBounds both
      | BothBounds both, OnlyLowerBound lower ->
          join lower both.lower >>| fun lower -> BothBounds { both with lower }
      | BothBounds left, BothBounds right -> (
          match meet left.upper right.upper, join left.lower right.lower with
          | Some upper, Some lower -> Some (BothBounds { upper; lower })
          | _ -> None )


    let merge_solution_in interval ~variable ~solution =
      let upper_bound, lower_bound =
        match interval with
        | NoBounds -> None, None
        | OnlyUpperBound upper -> Some upper, None
        | OnlyLowerBound lower -> None, Some lower
        | BothBounds { upper; lower } -> Some upper, Some lower
      in
      let smart_instantiate ordered_types =
        let instantiated = Solution.instantiate_ordered_types solution ordered_types in
        if Type.OrderedTypes.equal (ListVariadic.self_reference variable) instantiated then
          (* We don't want variables bounded by themselves *)
          None
        else
          Some instantiated
      in
      create
        ?upper_bound:(upper_bound >>= smart_instantiate)
        ?lower_bound:(lower_bound >>= smart_instantiate)
        ()


    let is_trivial interval ~variable:_ =
      match interval with
      | NoBounds -> true
      | _ -> false


    let free_variables interval =
      let bounds =
        match interval with
        | NoBounds -> []
        | OnlyUpperBound upper -> [upper]
        | OnlyLowerBound lower -> [lower]
        | BothBounds { upper; lower } -> [upper; lower]
      in
      let extract = function
        | Type.OrderedTypes.Any -> []
        | Concrete types -> List.concat_map types ~f:Type.Variable.all_free_variables
        | Concatenation concatenation ->
            let outer =
              Type.OrderedTypes.Concatenation.head concatenation
              @ Type.OrderedTypes.Concatenation.tail concatenation
              |> List.concat_map ~f:Type.Variable.all_free_variables
            in
            let inner = Type.OrderedTypes.Concatenation.variable concatenation in
            if Type.Variable.Variadic.List.is_free inner then
              ListVariadic inner :: outer
            else
              outer
      in
      List.concat_map bounds ~f:extract
  end

  module CallableParametersIntervalContainer = IntervalContainer.Make (CallableParametersInterval)
  module UnaryIntervalContainer = IntervalContainer.Make (UnaryTypeInterval)
  module ListVariadicIntervalContainer = IntervalContainer.Make (ListVariadicInterval)

  module VariadicTupleConstraints = struct
    include Record.VariadicTupleConstraints

    let instantiate variadic_tuple_constraints ~solution =
      let instantiate_variadic_constraint_pair { left_elements; right_elements } =
        {
          left_elements = List.map left_elements ~f:(Solution.instantiate solution);
          right_elements = List.map right_elements ~f:(Solution.instantiate solution);
        }
      in
      List.map variadic_tuple_constraints ~f:instantiate_variadic_constraint_pair


    let known_length_for ~unaries annotation =
      match annotation with
      | Type.Parametric
          { name = "pyre_extensions.Unpack"; parameters = [Single (Type.Variable variable)] }
        when Type.Variable.Unary.is_free variable ->
          let tuple_type_length annotation =
            match annotation with
            | Type.Tuple (Bounded (Concrete annotations))
              when List.is_empty (Type.Variable.all_free_variables annotation) ->
                Some (List.length annotations)
            | _ -> None
          in
          UnaryVariable.Map.find unaries variable
          >>= fun { lower_bound; upper_bound } ->
          Option.first_some (tuple_type_length lower_bound) (tuple_type_length upper_bound)
      | _ -> Some 1


    let strip_elements_of_known_length
        ({ unaries; _ } as constraints)
        ~order
        { left_elements; right_elements }
      =
      let has_free_variable =
        Type.exists ~predicate:(function
            | Type.Variable variable when Type.Variable.Unary.is_free variable -> true
            | _ -> false)
      in
      match
        ( List.exists left_elements ~f:has_free_variable,
          List.exists right_elements ~f:has_free_variable )
      with
      | false, true ->
          let pair_with_matching_left_elements (pairs, left_elements, should_continue) right_element
            =
            match known_length_for ~unaries right_element with
            | Some length when should_continue ->
                let left_prefix, left_rest = List.split_n left_elements length in
                if List.length left_prefix = length then
                  (Some left_prefix, right_element) :: pairs, left_rest, true
                else
                  (None, right_element) :: pairs, left_rest, false
            | _ -> pairs, left_elements, false
          in
          let pairs_for_right_prefix, remaining_left_elements, _ =
            List.fold
              right_elements
              ~init:([], left_elements, true)
              ~f:pair_with_matching_left_elements
          in
          let remaining_right_elements =
            List.drop right_elements (List.length pairs_for_right_prefix)
          in
          let pairs_for_right_suffix, remaining_left_elements, _ =
            List.fold
              (List.rev remaining_right_elements)
              ~init:([], List.rev remaining_left_elements, true)
              ~f:pair_with_matching_left_elements
          in
          let left_middle_portion = List.rev remaining_left_elements in
          let right_middle_portion =
            List.take
              remaining_right_elements
              (List.length remaining_right_elements - List.length pairs_for_right_suffix)
          in
          let add_bound_for_pair unaries (left_elements, right) =
            unaries
            >>= fun unaries ->
            match left_elements, right with
            | Some [left], Type.Variable right when Type.Variable.Unary.is_free right ->
                UnaryIntervalContainer.add_bound
                  ~order
                  ~variable:right
                  ~bound:left
                  ~is_lower_bound:true
                  unaries
            | ( Some left_elements,
                Type.Parametric
                  {
                    name = "pyre_extensions.Unpack";
                    parameters = [Single (Type.Variable variable)];
                  } )
              when Type.Variable.Unary.is_free variable ->
                UnaryIntervalContainer.add_bound
                  ~order
                  ~variable
                  ~bound:(Type.tuple left_elements)
                  ~is_lower_bound:true
                  unaries
            | Some [left], right ->
                Option.some_if (Order.always_less_or_equal order ~left ~right) unaries
            | _ -> None
          in
          let unaries_after_adding_bounds =
            List.fold
              (pairs_for_right_prefix @ pairs_for_right_suffix)
              ~init:(Some unaries)
              ~f:add_bound_for_pair
          in
          let add_new_variadic_constraint
              ({ unaries; _ } as constraints)
              { left_elements; right_elements }
            =
            match left_elements, right_elements with
            | ( _,
                [
                  Type.Parametric
                    {
                      name = "pyre_extensions.Unpack";
                      parameters = [Single (Type.Variable variable)];
                    };
                ] ) ->
                UnaryIntervalContainer.add_bound
                  ~order
                  ~variable
                  ~bound:(Type.tuple left_elements)
                  ~is_lower_bound:true
                  unaries
                >>| fun unaries -> { constraints with unaries }, None
            | _ ->
                Some
                  ( constraints,
                    Option.some_if
                      (not (List.is_empty left_elements && List.is_empty right_elements))
                      { left_elements; right_elements } )
          in
          let constraints_after_adding_unary_bounds =
            unaries_after_adding_bounds >>| fun unaries -> { constraints with unaries }
          in
          constraints_after_adding_unary_bounds
          >>= fun constraints ->
          add_new_variadic_constraint
            constraints
            { left_elements = left_middle_portion; right_elements = right_middle_portion }
      | _ -> None


    let add ({ unaries; _ } as constraints) ~order ~left_elements ~right_elements =
      let free_unaries annotation =
        Type.Variable.all_free_variables annotation
        |> List.filter_map ~f:(function
               | Type.Variable.Unary unary -> Some unary
               | _ -> None)
      in
      let all_free_unaries = List.concat_map ~f:free_unaries (left_elements @ right_elements) in
      let add_unary_to_container unaries unary =
        (* We merely want to include `unary` in the set of unaries. So, just add a trivial interval. *)
        unaries
        >>= UnaryIntervalContainer.add_bound
              ~order
              ~variable:unary
              ~bound:Type.Bottom
              ~is_lower_bound:true
      in
      List.fold all_free_unaries ~init:(Some unaries) ~f:add_unary_to_container
      >>= fun unaries ->
      strip_elements_of_known_length
        { constraints with unaries }
        ~order
        { left_elements; right_elements }
      >>| fun (constraints, new_variadic_constraint) ->
      match new_variadic_constraint with
      | Some new_variadic_constraint ->
          {
            constraints with
            variadic_tuple_constraints =
              new_variadic_constraint :: constraints.variadic_tuple_constraints;
          }
      | None -> constraints


    let update_on_unary ({ variadic_tuple_constraints; _ } as constraints) ~order ~variable =
      (order, variable, variadic_tuple_constraints) |> ignore;
      let simplify_variadic_constraint state variadic_constraint =
        state
        >>= fun (constraints, variadic_constraints) ->
        strip_elements_of_known_length ~order constraints variadic_constraint
        >>| fun (constraints, simplified_variadic_constraint) ->
        match simplified_variadic_constraint with
        | Some simplified_variadic_constraint ->
            constraints, simplified_variadic_constraint :: variadic_constraints
        | None -> constraints, variadic_constraints
      in
      List.fold
        variadic_tuple_constraints
        ~init:(Some (constraints, []))
        ~f:simplify_variadic_constraint
      >>| fun (constraints, variadic_tuple_constraints) ->
      { constraints with variadic_tuple_constraints }
  end

  type order = Order.t

  let add_bound
      ({ unaries; callable_parameters; list_variadics; _ } as constraints)
      ~order
      ~pair
      ~is_lower_bound
    =
    match pair with
    | Type.Variable.UnaryPair (variable, bound) ->
        UnaryIntervalContainer.add_bound unaries ~order ~variable ~bound ~is_lower_bound
        >>| (fun unaries -> { constraints with unaries })
        >>= VariadicTupleConstraints.update_on_unary ~order ~variable
    | Type.Variable.ParameterVariadicPair (variable, bound) ->
        CallableParametersIntervalContainer.add_bound
          callable_parameters
          ~order
          ~variable
          ~bound
          ~is_lower_bound
        >>| fun callable_parameters -> { constraints with callable_parameters }
    | Type.Variable.ListVariadicPair (variable, bound) ->
        ListVariadicIntervalContainer.add_bound
          list_variadics
          ~order
          ~variable
          ~bound
          ~is_lower_bound
        >>| fun list_variadics -> { constraints with list_variadics }


  let add_lower_bound = add_bound ~is_lower_bound:true

  let add_upper_bound = add_bound ~is_lower_bound:false

  let add_variadic_tuple_constraint constraints ~order ~left_elements ~right_elements =
    VariadicTupleConstraints.add constraints ~order ~left_elements ~right_elements


  let add_fallback_to_any ({ have_fallbacks; _ } as constraints) addition =
    { constraints with have_fallbacks = Set.add have_fallbacks addition }


  let merge_solution
      { unaries; variadic_tuple_constraints; callable_parameters; list_variadics; have_fallbacks }
      solution
    =
    {
      unaries = UnaryIntervalContainer.merge_solution unaries ~solution;
      variadic_tuple_constraints =
        VariadicTupleConstraints.instantiate variadic_tuple_constraints ~solution;
      callable_parameters =
        CallableParametersIntervalContainer.merge_solution callable_parameters ~solution;
      list_variadics = ListVariadicIntervalContainer.merge_solution list_variadics ~solution;
      have_fallbacks;
    }


  let apply_fallbacks solution ~have_fallbacks =
    let optional_add map key data =
      match Map.add map ~key ~data with
      | `Ok map -> map
      | `Duplicate -> map
    in
    let add_fallback ({ Solution.unaries; callable_parameters; list_variadics } as solution)
      = function
      | Type.Variable.Unary variable ->
          { solution with unaries = optional_add unaries variable Type.Any }
      | Type.Variable.ParameterVariadic variable ->
          {
            solution with
            callable_parameters = optional_add callable_parameters variable Type.Callable.Undefined;
          }
      | Type.Variable.ListVariadic variable ->
          {
            solution with
            list_variadics = optional_add list_variadics variable Type.OrderedTypes.Any;
          }
    in
    Set.to_list have_fallbacks |> List.fold ~init:solution ~f:add_fallback


  let solve constraints ~order =
    let rec build_solution ~remaining_constraints ~partial_solution =
      let independent_constraints, dependent_constraints =
        let independent_unaries, dependent_unaries =
          UnaryIntervalContainer.partition_independent_dependent
            remaining_constraints.unaries
            ~with_regards_to:remaining_constraints
        in
        let independent_parameters, dependent_parameters =
          CallableParametersIntervalContainer.partition_independent_dependent
            remaining_constraints.callable_parameters
            ~with_regards_to:remaining_constraints
        in
        let independent_list_variadics, dependent_list_variadics =
          ListVariadicIntervalContainer.partition_independent_dependent
            remaining_constraints.list_variadics
            ~with_regards_to:remaining_constraints
        in
        let independent_fallbacks, dependent_fallbacks =
          let matches = function
            | Type.Variable.Unary key -> not (Map.mem dependent_unaries key)
            | ParameterVariadic key -> not (Map.mem dependent_parameters key)
            | ListVariadic key -> not (Map.mem dependent_list_variadics key)
          in
          Set.partition_tf remaining_constraints.have_fallbacks ~f:matches
        in
        ( {
            unaries = independent_unaries;
            variadic_tuple_constraints = remaining_constraints.variadic_tuple_constraints;
            callable_parameters = independent_parameters;
            list_variadics = independent_list_variadics;
            have_fallbacks = independent_fallbacks;
          },
          {
            unaries = dependent_unaries;
            variadic_tuple_constraints = remaining_constraints.variadic_tuple_constraints;
            callable_parameters = dependent_parameters;
            list_variadics = dependent_list_variadics;
            have_fallbacks = dependent_fallbacks;
          } )
      in
      let handle_dependent_constraints partial_solution =
        let is_empty { unaries; callable_parameters; list_variadics; have_fallbacks; _ } =
          UnaryVariable.Map.is_empty unaries
          && ParameterVariable.Map.is_empty callable_parameters
          && ListVariadic.Map.is_empty list_variadics
          && Set.is_empty have_fallbacks
        in
        if is_empty dependent_constraints then
          Some partial_solution
        else if is_empty independent_constraints then
          None
        else
          let remaining_constraints = merge_solution dependent_constraints partial_solution in
          build_solution ~remaining_constraints ~partial_solution
      in
      UnaryIntervalContainer.add_solution independent_constraints.unaries partial_solution ~order
      >>= CallableParametersIntervalContainer.add_solution
            independent_constraints.callable_parameters
            ~order
      >>= ListVariadicIntervalContainer.add_solution independent_constraints.list_variadics ~order
      >>| apply_fallbacks ~have_fallbacks:independent_constraints.have_fallbacks
      >>= handle_dependent_constraints
    in
    build_solution ~remaining_constraints:constraints ~partial_solution:Solution.empty


  let extract_partial_solution
      { unaries; variadic_tuple_constraints; callable_parameters; list_variadics; have_fallbacks }
      ~order
      ~variables
    =
    let extracted_constraints, remaining_constraints =
      let unary_matches ~key ~data:_ =
        List.exists variables ~f:(Type.Variable.equal (Type.Variable.Unary key))
      in
      let callable_parameters_matches ~key ~data:_ =
        List.exists variables ~f:(Type.Variable.equal (Type.Variable.ParameterVariadic key))
      in
      let list_variadic_matches ~key ~data:_ =
        List.exists variables ~f:(Type.Variable.equal (Type.Variable.ListVariadic key))
      in
      let extracted_unaries, remaining_unaries =
        UnaryVariable.Map.partitioni_tf unaries ~f:unary_matches
      in
      let extracted_variadics, remaining_variadics =
        ParameterVariable.Map.partitioni_tf callable_parameters ~f:callable_parameters_matches
      in
      let extracted_list_variadics, remaining_list_variadics =
        ListVariadic.Map.partitioni_tf list_variadics ~f:list_variadic_matches
      in
      let extracted_fallbacks, remaining_fallbacks =
        let matches = function
          | Type.Variable.Unary key -> unary_matches ~key ~data:()
          | ParameterVariadic key -> callable_parameters_matches ~key ~data:()
          | ListVariadic key -> list_variadic_matches ~key ~data:()
        in
        Set.partition_tf have_fallbacks ~f:matches
      in
      ( {
          unaries = extracted_unaries;
          variadic_tuple_constraints;
          callable_parameters = extracted_variadics;
          list_variadics = extracted_list_variadics;
          have_fallbacks = extracted_fallbacks;
        },
        {
          unaries = remaining_unaries;
          variadic_tuple_constraints;
          callable_parameters = remaining_variadics;
          list_variadics = remaining_list_variadics;
          have_fallbacks = remaining_fallbacks;
        } )
    in
    solve extracted_constraints ~order
    >>| fun solution -> merge_solution remaining_constraints solution, solution
end
