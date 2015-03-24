# Graph search

`graphsearch` is a simple graph library for the rust programming language.
`graphsearch` can be used for basic representation and manipulation of
[graph structures](http://en.wikipedia.org/wiki/Graph_(abstract_data_type)). At the
moment featureset is quite limited.

## Organization
 - **README.md**  - The document you are currently reading.
 - **Cargo.toml** - The [cargo](https://crates.io/) definition for this package.
 - **src/lib.rs** - The actual implementation of this library.

## Features
 - Graphs with vertex costs
 - Breadth first search
 - Depth first search
 - Dijksras algorithm

## Usage example

Here's a short basic example of using this library as an external crate:

```
extern crate graphsearch;
use graphsearch::Graph;
fn main() {
  let testgraph = vec![vec![Some(0), Some(20), None],
                       vec![   None,  Some(0), Some(30)],
                       vec![   None,     None, Some(0)]];
  let start: usize = 0;
  let target: usize = 2;
  let g = Graph::new(testgraph);
  let res = g.search(start, target); // uses dijkstras algorithm
  match res {
    None => {
      println!("Search returned None");
    }
    Some(result) => {
      println!("Search returned a path: {:?}", result);
      println!("The returned path cost: {}", g.cost_of_path(&result));
    }
  }
}


```

## License

This project is licensed under the MIT license, a copy of which can be found in the
LICENCE file.
