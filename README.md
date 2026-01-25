# Idris2 Verified Sorting Algorithms

A collection of sorting algorithm implementations in Idris2 with formal correctness proofs. Each sorting algorithm comes with mathematical proofs that:
- The output is a permutation of the input (no elements are lost or duplicated)
- The output is sorted according to the given ordering relation

## Features

- **Formally Verified**: All sorting algorithms come with proofs of correctness
- **Generic**: Works with any type and any ordering relation (as long as it's strongly connected and transitive)
- **Multiple Algorithms**: Implementation of several classic sorting algorithms
- **Idris2 Type System**: Leverages dependent types for compile-time correctness guarantees

## Implemented Algorithms

### Insertion Sort
- Classic insertion sort algorithm
- Proof that output is sorted and a permutation of input
- Located in `src/Sort/InsertionSort.idr`

### Merge Sort
- Divide-and-conquer merge sort
- Uses well-founded recursion for totality checking
- Includes hybrid variant that switches to insertion sort for small sublists (threshold = 32)
- Located in `src/Sort/MergeSort.idr`

### Quick Sort
- Partition-based sorting algorithm
- Located in `src/Sort/QuickSort.idr`

### Tim Sort
- Hybrid sorting algorithm inspired by merge sort and insertion sort
- Located in `src/Sort/TimSort.idr`

### Selection Sort
- Simple selection sort algorithm
- Located in `src/Sort/SelectionSort.idr`

### Bubble Sort
- Classic bubble sort algorithm
- Located in `src/Sort/BubbleSort.idr`

### Gnome Sort
- Simple comparison-based sorting algorithm
- Located in `src/Sort/GnomeSort.idr`

## Project Structure

```
src/
├── Sort.idr                 # Main module, re-exports all sorting algorithms
├── Sort/                    # Sorting algorithm implementations
│   ├── InsertionSort.idr
│   ├── MergeSort.idr
│   ├── QuickSort.idr
│   ├── TimSort.idr
│   ├── SelectionSort.idr
│   ├── BubbleSort.idr
│   └── GnomeSort.idr
├── Proofs/                  # Proof modules
│   ├── Permutation.idr      # Permutation relation and proofs
│   ├── Permutation/
│   │   └── Relation.idr     # Permutation relation utilities
│   └── Sorted.idr           # Sorted predicate and proofs
└── Utils/                   # Utility modules
    ├── Relation.idr         # Relation utilities
    └── Vect.idr             # Vector utilities
```

## Usage

To use the sorting algorithms in your Idris2 project:

1. Add `sort` as a dependency in your `.ipkg` file:
   ```
   depends = base, contrib, sort
   ```

2. Import the module:
   ```idris
   import Sort
   ```

3. Use a sorting function:
   ```idris
   import Sort.InsertionSort
   import Data.Vect
   
   -- Sort a vector of natural numbers
   sorted : (v : Vect n Nat ** (Permutation input v, Sorted LTE v))
   sorted = insertionSort LTE [3, 1, 4, 1, 5, 9, 2, 6]
   ```

## Building

This project uses `pack` for dependency management:

```bash
# Build the project
pack build sort.ipkg

# Run tests
pack test sort.ipkg

# Install to pack's global collection
pack install sort
```

Alternatively, using Idris2 directly:

```bash
# Build
idris2 --build sort.ipkg

# Install
idris2 --install sort.ipkg
```

## Requirements

- Idris2 (tested with recent versions)
- Dependencies: `base`, `contrib`

## Mathematical Guarantees

Each sorting function returns a dependent pair containing:
1. The sorted vector
2. A proof that the result is a permutation of the input
3. A proof that the result satisfies the `Sorted` predicate

The type signature guarantees that:
```idris
sortingFunction : (rel : a -> a -> Type) 
               -> (StronglyConnex a rel, Transitive a rel) 
               => (xs : Vect n a) 
               -> (v : Vect n a ** (Permutation xs v, Sorted rel v))
```

This means:
- The length is preserved (`Vect n a` in, `Vect n a` out)
- The output is a permutation of input (no elements lost or added)
- The output satisfies the `Sorted` predicate for the given relation

## License

Apache License 2.0 - see [LICENSE](LICENSE) for details.

## Author

kimuti-tsukai
