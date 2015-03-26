use std::collections::VecDeque;
use std::collections::HashSet;
use std::collections::BinaryHeap;

use std::cmp::Ordering;


pub struct Node<T> {
  content: T,
  adjecent: Vec<Vertex>,
}

#[derive(Copy, Eq, PartialEq, Debug)]
pub struct Vertex {
  cost: i32,
  node: usize
}
// The priority queue depends on `Ord`.
// Explicitly implement the trait so the queue becomes a min-heap
// instead of a max-heap.
impl Ord for Vertex {
    fn cmp(&self, other: &Vertex) -> Ordering {
        // Notice that the we flip the ordering here
        other.cost.cmp(&self.cost)
        //self.cost.cmp(&other.cost)
    }
}

// `PartialOrd` needs to be implemented as well.
impl PartialOrd for Vertex {
    fn partial_cmp(&self, other: &Vertex) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}


/// A graph is represeted by as a weighted
/// [Adjenceny matrix](http://en.wikipedia.org/wiki/Adjacency_matrix)
pub struct Graph<T> {
  /// The underlaying graph represented here with weights as an i32 (should
  /// probably be generic) the graph is represented as an
  /// [Adjenceny matrix](http://en.wikipedia.org/wiki/Adjacency_matrix) of
  /// Optionals, where None indicates that there doesn't exist a vertex and
  /// Some<i32> indicates that There is a vertex of weight i32.
  graph: Vec<Node<T>>
}
impl <T> Graph<T> {
  /// `new` allows for initializing the graph struct with a given adjecency matrix
  ///
  /// ## Arguments
  /// * `input` - an adjecency matrix in made out of a two-dimensional `Vec` of
  ///    weights. Weights are represented as `i32`:s and can thus be positive or
  ///    negative numbers.
  ///
  /// ## Example
  /// ```ignore
  ///  let rawgraph = vec![vec![Some(0), Some(20), Some(80), Some(50),     None,     None],
  ///                      vec![   None,  Some(0),     None,     None,     None,     None],
  ///                      vec![   None,     None,  Some(0),     None,     None,     None],
  ///                      vec![   None,     None,     None,  Some(0), Some(50),     None],
  ///                      vec![   None,     None, Some(20),     None,  Some(0), Some(50)],
  ///                      vec![   None,     None,     None,     None,     None,  Some(0)]];
  /// let g = Graph::new(rawgraph);
  /// ```
  pub fn new(input: Vec<Node<T>>) -> Graph<T> {
    Graph { graph: input }
  }

  /// `search` promises to use a correct method, i.e. one which will return the
  /// _best_ path between `start` and `target` if there is a valid path between them.
  /// Which search method applied is not specified but currently Dijkstras algorithm
  /// is used. The path found is returned as a `VecDeque<usize>` of nodes. The
  /// `VecDeque<usize>` is an optional type as there might not be a path.
  ///
  /// ## Arguments
  /// * `start`  - an `usize` designating the start node, or row in the adjecency matrix
  /// * `target` - an `usize` designating the target node, or row in the adjecency matrix
  ///
  /// ## Returns
  /// Either the found path between start and target as a `VecDeque` of `usize`:s
  /// or `None` if there is no path.
  pub fn search(&self, start: usize, target: usize) -> Option<VecDeque<usize>> {
    return self.dijkstra(start, target)
  }
  /// `breadth_first_search` implements breadth first search from `start` to the
  /// `target` and returns the path found as a `VecDeque<usize>` of nodes. This
  /// is an optional type as there might not be a path.
  ///
  /// **NOTE** as this is breadth first search this search ignores any assigned
  /// weight to nodes.
  ///
  /// ## Arguments
  /// * `start`  - an `usize` designating the start node, or row in the adjecency matrix
  /// * `target` - an `usize` designating the target node, or row in the adjecency matrix
  ///
  /// ## Returns
  /// Either the found path between start and target as a `VecDeque` of `usize`:s
  /// or `None` if there is no path.
  pub fn breadth_first_search(&self, start: usize, target: usize) -> Option<VecDeque<usize>> {
    return self.inner_search(start, target, true)
  }

  /// `depth_first_search` implements depth first search from `start` to the
  /// `target` and returns the path found as a `VecDeque<usize>` of nodes. This
  /// is an optional type as there might not be a path.
  ///
  /// **NOTE** as this is depth first search this search ignores any assigned
  /// weight to nodes.
  ///
  /// ## Arguments
  /// * `start`  - an `usize` designating the start node, or row in the adjecency matrix
  /// * `target` - an `usize` designating the target node, or row in the adjecency matrix
  ///
  /// ## Returns
  /// Either the found path between start and target as a `VecDeque` of `usize`:s
  /// or `None` if there is no path.
  pub fn depth_first_search(&self, start: usize, target: usize) -> Option<VecDeque<usize>> {
    return self.inner_search(start, target, false)
  }

  /// `dijkstra` implements Dijkstras algorithm for search from `start` to the
  /// `target` and returns the path found as a `VecDeque<usize>` of nodes. This
  /// is an optional type as there might not be a path.
  ///
  /// ## Arguments
  /// * `start`  - an `usize` designating the start node, or row in the adjecency matrix
  /// * `target` - an `usize` designating the target node, or row in the adjecency matrix
  ///
  /// ## Returns
  /// Either the found path between start and target as a `VecDeque` of `usize`:s
  /// or `None` if there is no path.
  pub fn dijkstra(&self, start: usize, target: usize) -> Option<VecDeque<usize>> {
    let mut q = BinaryHeap::new();
    let mut costs: Vec<_> = (0..self.graph.len()).map(|_| std::i32::MAX).collect();
    let mut prev: Vec<usize> = (0..self.graph.len()).map(|_| 0).collect();
    let mut pathfound = false;

    costs[start] = 0;
    q.push(Vertex {cost: 0, node: start});

    while !q.is_empty() {
      let v = q.pop();
      match v {
        None => {},
        Some(Vertex {cost, node}) => {
          if node == target { println!("Target found"); pathfound = true; }
          if cost > costs[node] { continue; } // we have a better path
          for vert in &self.graph[node].adjecent {
            let next = Vertex { cost: cost+vert.cost, node: vert.node };
            if next.cost < costs[vert.node] {
              q.push(next);
              costs[vert.node] = next.cost;
              prev[vert.node] = node;
            }
          }
        }
      }
    }
    if pathfound { return Some(self.backtrack(prev, start, target)) }
    return None
  }

  /// `cost_of_path` takes a path returned from any of the search functions and
  /// calculates the cost of the path.
  ///
  /// ## Arguments
  /// * `path` - a borrowed reference to a `VecDeque<usize>` representing a path
  ///            through the graph
  ///
  /// ## Returns
  /// The cost of traversing said path represented as an `i32`
  pub fn cost_of_path(&self, path: &VecDeque<usize>) -> i32 {
    let mut cost = 0;
    for i in (0..path.len()-1) {
      for vert in &self.graph[path[i]].adjecent {
        if vert.node==path[i+1] { cost = cost + vert.cost; }
      }
    }
    return cost
  }

  fn inner_search(&self, start: usize, target: usize, bfs: bool) -> Option<VecDeque<usize>>  {
    let mut q = VecDeque::new();
    let mut discovered: HashSet<usize> = HashSet::new();
    let mut prev: Vec<usize> = (0..self.graph.len()).map(|_| 0).collect();
    let mut pathfound = false;

    q.push_back(start);
    discovered.insert(start);

   while !q.is_empty() {
      let mut v: Option<usize>;
      if bfs {
        v = q.pop_front()
      } else {
        v = q.pop_back();
      }
      match v {
        None => {}, // q is empty
        Some(v) => { // we are working on a new layer
          if !discovered.contains(&v) { discovered.insert(v); }
          if v == target { pathfound = true; }
          for vertex in &self.graph[v].adjecent {
            if !discovered.contains(&vertex.node) {
              q.push_back(vertex.node);
              prev[vertex.node]=v; //track prev (v) on i
            }
          }
        }
      }
    }
    if pathfound { return Some(self.backtrack(prev, start, target)) }
    return None
  }

  /// `backtrack` is a simple function for traversing the graph from `target` to
  /// `start` using the path indicated by the `prev` Vec.
  ///
  /// ## Returns
  /// Returns a the path between `start` and `target` as a `VecDeque<usize>`.
  fn backtrack(&self, prev: Vec<usize>, start: usize, target: usize) -> VecDeque<usize> {
      let mut path: VecDeque<usize> = VecDeque::new();
      let mut curr = target;
      // backtrack over the prev array to construct the path
      while curr != start {
        path.push_front(curr);
        curr = prev[curr];
      }
      path.push_front(start);
      return path
  }
}


#[test]
fn search_test() {
  let testgraph = vec![Node{content: 0, adjecent: vec![Vertex{cost: 20, node: 1}, Vertex{cost: 50, node: 2}, Vertex{cost: 10, node: 3}]},
                       Node{content: 1, adjecent: Vec::new()},
                       Node{content: 2, adjecent: vec![Vertex{cost: 50, node: 6}]},
                       Node{content: 3, adjecent: vec![Vertex{cost: 20, node: 4}]},
                       Node{content: 4, adjecent: vec![Vertex{cost: 20, node: 3}, Vertex{cost: 50, node: 3}, Vertex{cost: 30, node: 6}]},
                       Node{content: 5, adjecent: Vec::new()},
                       Node{content: 6, adjecent: Vec::new()}];
  let start: usize = 0;
  let target: usize = 6;
  let g = Graph::new(testgraph);
  let res = g.search(start, target);
  match res {
    None => {
      println!("Search returned None");
      assert!(false);
    }
    Some(result) => {
      println!("Search returned something: {:?}", result);
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
    }
  }
}

#[test]
fn search_test_no_valid_path() {
  let testgraph = vec![Node{content: 0, adjecent: vec![Vertex{cost: 20, node: 1}, Vertex{cost: 50, node: 2}, Vertex{cost: 10, node: 3}]},
                       Node{content: 1, adjecent: Vec::new()},
                       Node{content: 2, adjecent: vec![Vertex{cost: 50, node: 6}]},
                       Node{content: 3, adjecent: vec![Vertex{cost: 20, node: 4}]},
                       Node{content: 4, adjecent: vec![Vertex{cost: 20, node: 3}, Vertex{cost: 50, node: 3}, Vertex{cost: 30, node: 6}]},
                       Node{content: 5, adjecent: Vec::new()},
                       Node{content: 6, adjecent: Vec::new()}];
  let start: usize = 0;
  let target: usize = 5; // There is no valid path between 0 and 5
  let g = Graph::new(testgraph);
  let res = g.search(start, target);

  // The expected return value is None
  match res {
    None => {
      println!("Search returned None");
      assert!(true);
    }
    Some(result) => {
      println!("Search returned something: {:?}", result);
      println!("The returned path cost: {}", g.cost_of_path(&result));
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
      assert!(false);
    }
  }
}

#[test]
fn breadth_first_search_test() {
  let testgraph = vec![Node{content: 0, adjecent: vec![Vertex{cost: 20, node: 1}, Vertex{cost: 50, node: 2}, Vertex{cost: 10, node: 3}]},
                       Node{content: 1, adjecent: Vec::new()},
                       Node{content: 2, adjecent: vec![Vertex{cost: 50, node: 6}]},
                       Node{content: 3, adjecent: vec![Vertex{cost: 20, node: 4}]},
                       Node{content: 4, adjecent: vec![Vertex{cost: 20, node: 3}, Vertex{cost: 50, node: 3}, Vertex{cost: 30, node: 6}]},
                       Node{content: 5, adjecent: Vec::new()},
                       Node{content: 6, adjecent: Vec::new()}];
  let start: usize = 0;
  let target: usize = 6;
  let g = Graph::new(testgraph);
  let res = g.breadth_first_search(start, target);
  match res {
    None => {
      println!("Breadth first search returned None");
      assert!(false);
    }
    Some(result) => {
      println!("Breadth first search returned something: {:?}", result);
      println!("The cost of path is: {}", g.cost_of_path(&result));
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
      for i in (0..expected_path.len()) { assert_eq!(result[i], expected_path[i]); }
      assert_eq!(expected_cost, g.cost_of_path(&result));
    }
  }
}

#[test]
fn breadth_first_search_test_no_valid_path() {
  let testgraph = vec![Node{content: 0, adjecent: vec![Vertex{cost: 20, node: 1}, Vertex{cost: 50, node: 2}, Vertex{cost: 10, node: 3}]},
                       Node{content: 1, adjecent: Vec::new()},
                       Node{content: 2, adjecent: vec![Vertex{cost: 50, node: 6}]},
                       Node{content: 3, adjecent: vec![Vertex{cost: 20, node: 4}]},
                       Node{content: 4, adjecent: vec![Vertex{cost: 20, node: 3}, Vertex{cost: 50, node: 3}, Vertex{cost: 30, node: 6}]},
                       Node{content: 5, adjecent: Vec::new()},
                       Node{content: 6, adjecent: Vec::new()}];
  let start: usize = 0;
  let target: usize = 5; // There is no valid path between 0 and 5
  let g = Graph::new(testgraph);
  let res = g.breadth_first_search(start, target);

  // The expected return value is None
  match res {
    None => {
      println!("Breadth first search returned None");
      assert!(true);
    }
    Some(result) => {
      println!("Breadth first search returned something: {:?}", result);
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
      assert!(false);
    }
  }
}

#[test]
fn depth_first_search_test() {
  let testgraph = vec![Node{content: 0, adjecent: vec![Vertex{cost: 20, node: 1}, Vertex{cost: 50, node: 2}, Vertex{cost: 10, node: 3}]},
                       Node{content: 1, adjecent: Vec::new()},
                       Node{content: 2, adjecent: vec![Vertex{cost: 50, node: 6}]},
                       Node{content: 3, adjecent: vec![Vertex{cost: 20, node: 4}]},
                       Node{content: 4, adjecent: vec![Vertex{cost: 20, node: 3}, Vertex{cost: 50, node: 3}, Vertex{cost: 30, node: 6}]},
                       Node{content: 5, adjecent: Vec::new()},
                       Node{content: 6, adjecent: Vec::new()}];
  let start: usize = 0;
  let target: usize = 6;
  let g = Graph::new(testgraph);
  let res = g.depth_first_search(start, target);
  match res {
    None => {
      println!("Depth first search returned None");
      assert!(false);
    }
    Some(result) => {
      println!("Depth first search returned something: {:?}", result);
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
    }
  }
}

#[test]
fn depth_first_search_test_no_valid_path() {
  let testgraph = vec![Node{content: 0, adjecent: vec![Vertex{cost: 20, node: 1}, Vertex{cost: 50, node: 2}, Vertex{cost: 10, node: 3}]},
                       Node{content: 1, adjecent: Vec::new()},
                       Node{content: 2, adjecent: vec![Vertex{cost: 50, node: 6}]},
                       Node{content: 3, adjecent: vec![Vertex{cost: 20, node: 4}]},
                       Node{content: 4, adjecent: vec![Vertex{cost: 20, node: 3}, Vertex{cost: 50, node: 3}, Vertex{cost: 30, node: 6}]},
                       Node{content: 5, adjecent: Vec::new()},
                       Node{content: 6, adjecent: Vec::new()}];
  let start: usize = 0;
  let target: usize = 5; // There is no valid path between 0 and 5
  let g = Graph::new(testgraph);
  let res = g.depth_first_search(start, target);

  // The expected return value is None
  match res {
    None => {
      println!("Depth first search returned None");
      assert!(true);
    }
    Some(result) => {
      println!("Depth first search returned something: {:?}", result);
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
      assert!(false);
    }
  }
}

#[test]
fn dijkstra_test() {
  let testgraph = vec![Node{content: 0, adjecent: vec![Vertex{cost: 20, node: 1}, Vertex{cost: 50, node: 2}, Vertex{cost: 10, node: 3}]},
                       Node{content: 1, adjecent: Vec::new()},
                       Node{content: 2, adjecent: vec![Vertex{cost: 50, node: 6}]},
                       Node{content: 3, adjecent: vec![Vertex{cost: 20, node: 4}]},
                       Node{content: 4, adjecent: vec![Vertex{cost: 20, node: 3}, Vertex{cost: 50, node: 3}, Vertex{cost: 30, node: 6}]},
                       Node{content: 5, adjecent: Vec::new()},
                       Node{content: 6, adjecent: Vec::new()}];
  let start: usize = 0;
  let target: usize = 6;
  let g = Graph::new(testgraph);
  let res = g.dijkstra(start, target);
  match res {
    None => {
      println!("Dijkstra search returned None");
      assert!(false);
    }
    Some(result) => {
      println!("Dijkstra returned something: {:?}", result);
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
    }
  }
}

#[test]
fn dijkstra_test_no_valid_path() {
  let testgraph = vec![Node{content: 0, adjecent: vec![Vertex{cost: 20, node: 1}, Vertex{cost: 50, node: 2}, Vertex{cost: 10, node: 3}]},
                       Node{content: 1, adjecent: Vec::new()},
                       Node{content: 2, adjecent: vec![Vertex{cost: 50, node: 6}]},
                       Node{content: 3, adjecent: vec![Vertex{cost: 20, node: 4}]},
                       Node{content: 4, adjecent: vec![Vertex{cost: 20, node: 3}, Vertex{cost: 50, node: 3}, Vertex{cost: 30, node: 6}]},
                       Node{content: 5, adjecent: Vec::new()},
                       Node{content: 6, adjecent: Vec::new()}];
  let start: usize = 0;
  let target: usize = 5; // There is no valid path between 0 and 5
  let g = Graph::new(testgraph);
  let res = g.dijkstra(start, target);

  // The expected return value is None
  match res {
    None => {
      println!("Dijkstra returned None");
      assert!(true);
    }
    Some(result) => {
      println!("Dijkstra returned something: {:?}", result);
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
      assert!(false);
    }
  }
}
