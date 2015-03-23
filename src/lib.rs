use std::collections::VecDeque;
use std::collections::HashSet;
use std::collections::BinaryHeap;

use std::cmp::Ordering;

#[derive(Copy, Eq, PartialEq, Debug)]
struct State {
    cost: i32,
    position: usize,
}

// The priority queue depends on `Ord`.
// Explicitly implement the trait so the queue becomes a min-heap
// instead of a max-heap.
impl Ord for State {
    fn cmp(&self, other: &State) -> Ordering {
        // Notice that the we flip the ordering here
        other.cost.cmp(&self.cost)
        //self.cost.cmp(&other.cost)
    }
}

// `PartialOrd` needs to be implemented as well.
impl PartialOrd for State {
    fn partial_cmp(&self, other: &State) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}


/// A graph is represeted by as a weighted
/// [Adjenceny matrix](http://en.wikipedia.org/wiki/Adjacency_matrix)
pub struct Graph {
  /// The underlaying graph represented here with weights as an i32 (should
  /// probably be generic) the graph is represented as an
  /// [Adjenceny matrix](http://en.wikipedia.org/wiki/Adjacency_matrix) of
  /// Optionals, where None indicates that there doesn't exist a vertex and
  /// Some<i32> indicates that There is a vertex of weight i32.
  graph: Vec<Vec<Option<i32>>>
}
impl Graph {
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
  pub fn new(input: Vec<Vec<Option<i32>>>) -> Graph { Graph { graph: input } }

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

  fn inner_search(&self, start: usize, target: usize, bfs: bool) -> Option<VecDeque<usize>>  {
    let mut q: VecDeque<usize> = VecDeque::new();
    let mut discovered: HashSet<usize> = HashSet::new();
    let mut prev: Vec<usize> = Vec::with_capacity(self.graph.len());
    let mut pathfound = false;
    for _ in (0..self.graph.len()) { prev.push(0); }

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
          for i in (0..self.graph[v].len()) {
            match self.graph[v][i] {
              None => {}, // no vertex between v and i
              Some(_) => {
                if !discovered.contains(&i) {
                  q.push_back(i);
                  prev[i]=v; //track prev (v) on i
                }
              }
            }
          }
        }
      }
    }
    if pathfound {
      let mut path: VecDeque<usize> = VecDeque::new();
      let mut curr = target;
      // backtrack over the prev array to construct the path
      while curr != start {
        path.push_front(curr);
        curr = prev[curr];
      }
      path.push_front(start);
      return Some(path)
    }
    return None
  }

  pub fn dijkstra(&self, start: usize, target: usize) -> Option<VecDeque<usize>> {
    let mut costs: Vec<_> = (0..self.graph.len()).map(|_| std::i32::MAX).collect();
    let mut heap = BinaryHeap::new();
    let mut prev: Vec<usize> = Vec::with_capacity(self.graph.len());
    for _ in (0..self.graph.len()) { prev.push(0); }
    let mut pathfound = false;

    costs[start] = 0;
    heap.push(State {cost: 0, position: start});

    while !heap.is_empty() {
      let v = heap.pop();
      match v {
        None => {},
        Some(State {cost, position}) => {
          if position == target { println!("Target found"); pathfound = true; }
          if cost > costs[position] { continue; } // we have a better path
          for i in (0..self.graph[position].len()) {
            match self.graph[position][i] {
              None => {}, // no vertex between position on i
              Some(c) => {
                let next = State { cost: cost+c, position: i };
                if next.cost < costs[i] {
                  heap.push(next);
                  costs[i] = next.cost;
                  prev[i] = position;
                }
              }
            }
          }
        }
      }
    }
    if pathfound {
      let mut path: VecDeque<usize> = VecDeque::new();
      let mut curr = target;
      // backtrack over the prev array to construct the path
      while curr != start {
        path.push_front(curr);
        curr = prev[curr];
      }
      path.push_front(start);
      return Some(path)
    }
    return None
  }

  /// `cost_of_path` takes a path returned from any of the search functions and
  /// calculates the cost of the path.
  ///
  /// ## Arguments
  /// * `path` - a `VecDeque<usize>` representing a path through the graph
  ///
  /// ## Returns
  /// The cost of traversing said path represented as an `i32`
  pub fn cost_of_path(&self, path: VecDeque<usize>) -> i32 {
    let mut cost = 0;
    for i in (0..path.len()-1) {
      match self.graph[path[i]][path[i+1]] {
        None => {},
        Some(c) => { cost = cost + c; }
      }
    }
    return cost
  }
}


#[test]
fn breadth_first_search_test() {
  let testgraph = vec![vec![Some(0), Some(20), Some(80), Some(50),     None,     None, None],
                       vec![   None,  Some(0),     None,     None,     None,     None, None],
                       vec![   None,     None,  Some(0),     None,     None,     None,  Some(50)],
                       vec![   None,     None,     None,  Some(0), Some(50),     None, None],
                       vec![   None,     None, Some(20),     None,  Some(0), Some(50),  Some(40)],
                       vec![   None,     None,     None,     None,     None,  Some(0), None],
                       vec![   None,     None,     None,     None,     None,     None, Some(0)]];
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
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
    }
  }
}

#[test]
fn breadth_first_search_test_no_valid_path() {
  let testgraph = vec![vec![Some(0), Some(20), Some(80), Some(50),     None,     None, None],
                       vec![   None,  Some(0),     None,     None,     None,     None, None],
                       vec![   None,     None,  Some(0),     None,     None,     None,  Some(50)],
                       vec![   None,     None,     None,  Some(0), Some(50),     None, None],
                       vec![   None,     None, Some(20),     None,  Some(0),     None,  Some(40)],
                       vec![   None,     None,     None,     None,     None,  Some(0), None],
                       vec![   None,     None,     None,     None,     None,     None, Some(0)]];
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
  let testgraph = vec![vec![Some(0), Some(20), Some(80), Some(50),     None,     None, None],
                       vec![   None,  Some(0),     None,     None,     None,     None, None],
                       vec![   None,     None,  Some(0),     None,     None,     None,  Some(50)],
                       vec![   None,     None,     None,  Some(0), Some(50),     None, None],
                       vec![   None,     None, Some(20),     None,  Some(0), Some(50),  Some(40)],
                       vec![   None,     None,     None,     None,     None,  Some(0), None],
                       vec![   None,     None,     None,     None,     None,     None, Some(0)]];
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
  let testgraph = vec![vec![Some(0), Some(20), Some(80), Some(50),     None,     None, None],
                       vec![   None,  Some(0),     None,     None,     None,     None, None],
                       vec![   None,     None,  Some(0),     None,     None,     None,  Some(50)],
                       vec![   None,     None,     None,  Some(0), Some(50),     None, None],
                       vec![   None,     None, Some(20),     None,  Some(0),     None,  Some(40)],
                       vec![   None,     None,     None,     None,     None,  Some(0), None],
                       vec![   None,     None,     None,     None,     None,     None, Some(0)]];
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
  let testgraph = vec![vec![Some(0), Some(20), Some(50), Some(10),     None,     None, None],
                       vec![   None,  Some(0),     None,     None,     None,     None, None],
                       vec![   None,     None,  Some(0),     None,     None,     None,  Some(50)],
                       vec![   None,     None,     None,  Some(0), Some(20),     None, None],
                       vec![   None,     None, Some(20),     None,  Some(0), Some(50),  Some(30)],
                       vec![   None,     None,     None,     None,     None,  Some(0), None],
                       vec![   None,     None,     None,     None,     None,     None, Some(0)]];
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
  let testgraph = vec![vec![Some(0), Some(20), Some(80), Some(50),     None,     None, None],
                       vec![   None,  Some(0),     None,     None,     None,     None, None],
                       vec![   None,     None,  Some(0),     None,     None,     None,  Some(50)],
                       vec![   None,     None,     None,  Some(0), Some(50),     None, None],
                       vec![   None,     None, Some(20),     None,  Some(0),     None,  Some(40)],
                       vec![   None,     None,     None,     None,     None,  Some(0), None],
                       vec![   None,     None,     None,     None,     None,     None, Some(0)]];
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
