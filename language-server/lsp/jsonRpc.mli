(**************************************************************************)
(*                                                                        *)
(*                                 VSCoq                                  *)
(*                                                                        *)
(*                   Copyright INRIA and contributors                     *)
(*       (see version control and README file for authors & dates)        *)
(*                                                                        *)
(**************************************************************************)
(*                                                                        *)
(*   This file is distributed under the terms of the MIT License.         *)
(*   See LICENSE file.                                                    *)
(*                                                                        *)
(**************************************************************************)
module Notification :
  sig
    type t = { method_ : string; params : Yojson.Safe.t; }
    val yojson_of_t : t -> Yojson.Safe.t
  end

module Request :
  sig
    type t = { id : int; method_ : string; params : Yojson.Safe.t; }
    val yojson_of_t : t -> Yojson.Safe.t
  end

module Response : sig

module Error : sig

  type t = { code : int; message : string } [@@deriving yojson]

end

type t = { id : int; result : (Yojson.Safe.t, Error.t) Result.t }
val yojson_of_t : t -> Yojson.Safe.t

end