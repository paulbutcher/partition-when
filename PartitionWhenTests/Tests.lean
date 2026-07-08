import PartitionWhen.Basic

#guard [1, 2, 0, 3, 4, 0, 5].partitionWhen (· == 0) == [[1, 2], [0, 3, 4], [0, 5]]
#guard ([] : List Nat).partitionWhen (· == 0) == []
#guard [0, 1, 2].partitionWhen (· == 0) == [[0, 1, 2]]
#guard [1, 2, 3].partitionWhen (· == 0) == [[1, 2, 3]]
#guard [0, 0, 0].partitionWhen (· == 0) == [[0], [0], [0]]

#guard [1, 2, 0, 3, 4, 0, 5].partitionWhenTR (· == 0) == [[1, 2], [0, 3, 4], [0, 5]]
#guard ([] : List Nat).partitionWhenTR (· == 0) == []
#guard [0, 1, 2].partitionWhenTR (· == 0) == [[0, 1, 2]]
#guard [1, 2, 3].partitionWhenTR (· == 0) == [[1, 2, 3]]
#guard [0, 0, 0].partitionWhenTR (· == 0) == [[0], [0], [0]]

#guard [1, 2, 0, 3, 4, 0, 5].partitionWhenFold (· == 0) == [[1, 2], [0, 3, 4], [0, 5]]
#guard ([] : List Nat).partitionWhenFold (· == 0) == []
#guard [0, 1, 2].partitionWhenFold (· == 0) == [[0, 1, 2]]
#guard [1, 2, 3].partitionWhenFold (· == 0) == [[1, 2, 3]]
#guard [0, 0, 0].partitionWhenFold (· == 0) == [[0], [0], [0]]

#guard [1, 2, 0, 3, 4, 0, 5].partitionWhenTake (· == 0) == [[1, 2], [0, 3, 4], [0, 5]]
#guard ([] : List Nat).partitionWhenTake (· == 0) == []
#guard [0, 1, 2].partitionWhenTake (· == 0) == [[0, 1, 2]]
#guard [1, 2, 3].partitionWhenTake (· == 0) == [[1, 2, 3]]
#guard [0, 0, 0].partitionWhenTake (· == 0) == [[0], [0], [0]]

#guard [1, 2, 0, 3, 4, 0, 5].partitionWhenSpan (· == 0) == [[1, 2], [0, 3, 4], [0, 5]]
#guard ([] : List Nat).partitionWhenSpan (· == 0) == []
#guard [0, 1, 2].partitionWhenSpan (· == 0) == [[0, 1, 2]]
#guard [1, 2, 3].partitionWhenSpan (· == 0) == [[1, 2, 3]]
#guard [0, 0, 0].partitionWhenSpan (· == 0) == [[0], [0], [0]]
