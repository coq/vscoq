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
type sentence_id = Stateid.t
type sentence_id_set = Stateid.Set.t

type link = {
  write_to :  Unix.file_descr;
  read_from:  Unix.file_descr;
}

type 'a log = Log : 'a -> 'a log
