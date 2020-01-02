Tc: Kind
Tc = Type -> Type

Tc2: Kind
Tc2 = Type -> Type -> Type

Mappable2: Tc2 -> Type
Mappable2 F = (X1: Type) -> (X2: Type) -> (Y1: Type) -> (Y2: Type) -> \
  (X1 -> X2) -> (Y1 -> Y2) -> F X1 Y1 -> F X2 Y2

map_fst: (F: Tc2) -> Mappable2 F -> (X1: Type) -> (X2: Type) -> (Y: Type) -> \
  (X1 -> X2) -> F X1 Y -> F X2 Y
map_fst F map2 X1 X2 Y f = map2 X1 X2 Y Y f (id Y)
map_snd: (F: Tc2) -> Mappable2 F -> (X: Type) -> Mappable (F X)
map_snd F map2 X Y1 Y2 f = map2 X X Y1 Y2 (id X) f

Rec2_Snd_Partial: Tc2 -> Tc
Rec2_Snd_Partial G X = Rec (G X)

Rec2_Fst_Partial: Tc2 -> Tc2 -> Tc
Rec2_Fst_Partial F G X = F X (Rec2_Snd_Partial G X)

Rec2_Fst: Tc2 -> Tc2 -> Type
Rec2_Fst F G = Rec (Rec2_Fst_Partial F G)

Rec2_Snd: Tc2 -> Tc2 -> Type
Rec2_Snd F G = Rec (G (Rec2_Fst F G))

Rec2_Snd_Partial_map_method: (G: Tc2) -> Mappable2 G -> \
  (X1: Type) -> (X2: Type) -> (X1 -> X2) -> G X1 (Rec (G X2)) -> Rec (G X2)
Rec2_Snd_Partial_map_method G gmap X1 X2 f x = Rec_close (G X2) \
  (map_snd G gmap X2) \
  (map_fst G gmap X1 X2 (Rec (G X2)) f x)
Rec2_Snd_Partial_map: (G: Tc2) -> Mappable2 G -> Mappable (Rec2_Snd_Partial G)
Rec2_Snd_Partial_map G gmap X1 X2 f = \
  Rec_fold (G X1) (map_snd G gmap X1) (Rec (G X2)) \
  (Rec2_Snd_Partial_map_method G gmap X1 X2 f)

Rec2_Fst_map: (F: Tc2) -> (G: Tc2) -> Mappable2 F -> Mappable2 G -> \
  Mappable (Rec2_Fst_Partial F G)
Rec2_Fst_map F G fmap gmap X1 X2 f = fmap X1 X2 (Rec (G X1)) (Rec (G X2)) \
  f (Rec2_Snd_Partial_map G gmap X1 X2 f)

Rec2_Snd_map: (F: Tc2) -> (G: Tc2) -> \
  Mappable2 G -> Mappable (G (Rec2_Fst F G))
Rec2_Snd_map F G gmap = map_snd G gmap (Rec2_Fst F G)


Rec2_Fst_open: (F: Tc2) -> (G: Tc2) -> Mappable2 F -> Mappable2 G -> \
  Rec2_Fst F G -> F (Rec2_Fst F G) (Rec2_Snd F G)
Rec2_Fst_open F G fmap gmap = Rec_open (Rec2_Fst_Partial F G) \
  (Rec2_Fst_map F G fmap gmap)
Rec2_Fst_close: (F: Tc2) -> (G: Tc2) -> Mappable2 F -> Mappable2 G -> \
  F (Rec2_Fst F G) (Rec2_Snd F G) -> Rec2_Fst F G
Rec2_Fst_close F G fmap gmap = Rec_close (Rec2_Fst_Partial F G) \
  (Rec2_Fst_map F G fmap gmap)

Rec2_Snd_open: (F: Tc2) -> (G: Tc2) -> Mappable2 G -> \
  Rec2_Snd F G -> G (Rec2_Fst F G) (Rec2_Snd F G)
Rec2_Snd_open F G gmap = Rec_open (G (Rec2_Fst F G)) (Rec2_Snd_map F G gmap)
Rec2_Snd_close: (F: Tc2) -> (G: Tc2) -> Mappable2 G -> \
  G (Rec2_Fst F G) (Rec2_Snd F G) -> Rec2_Snd F G
Rec2_Snd_close F G gmap = Rec_close (G (Rec2_Fst F G)) (Rec2_Snd_map F G gmap)

