Require Import Coq.Lists.List.
Import ListNotations.

Definition BotName := nat.
Definition NVSEntry := nat.

Goal exists (e' : NVSEntry), In (1, e') [(1, 2); (3, 4)].
Proof.
  exists 2.
  simpl.
  left.
  reflexivity.
Qed.