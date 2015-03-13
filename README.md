# Graph

_Graph_ is a simple graph library for the rust programming language. Graph can be
used for basic representation and manipulation of
[graph structures](http://en.wikipedia.org/wiki/Graph_%28mathematics%29). Currently the
featureset is limited.

## Organization
 - **README.md**  - The document you are currently reading.
 - **Cargo.toml** - The [cargo](https://crates.io/) definition for this package.
 - **src/lib.rs** - The actual implementation of this library.

## Features
 - Graphs with vertex costs
 - Breadth first search
 - Depth first search

## Todo
 - Implement a priority queue for use in the `inner_search` function. This will
   enable implementation of best first search.

## License

This project is licensed under the MIT license, a copy of which can be found in the
LICENCE file.
