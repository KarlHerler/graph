use std::collections::VecDeque;
use std::collections::HashSet;

/// A graph is represeted by as a weighted
/// [Adjenceny matrix](http://en.wikipedia.org/wiki/Adjacency_matrix)
struct Graph {
  graph: Vec<Vec<Option<i32>>>
}
impl Graph {
  fn new(input: Vec<Vec<Option<i32>>>) -> Graph { Graph { graph: input } }

  /*
  1  procedure BFS(G,v) is
  2      let Q be a queue
  3      Q.push(v)
  4      label v as discovered
  5      while Q is not empty
  6         v ← Q.pop()
  7         for all edges from v to w in G.adjacentEdges(v) do
  8             if w is not labeled as discovered
  9                 Q.push(w)
  10                label w as discovered
  */
  fn bfs(&self, start: usize, target: usize) -> Option<VecDeque<usize>> {
    let mut q: VecDeque<usize> = VecDeque::new();
    let mut discovered: HashSet<usize> = HashSet::new();
    let mut prev: Vec<usize> = Vec::with_capacity(self.graph.len());
    let mut pathfound = false;
    for _ in (0..self.graph.len()) { prev.push(0); }

    q.push_back(start);
    discovered.insert(start);
    //println!("q size: {} and is empty: {}", q.len(), q.is_empty());

    while !q.is_empty() {
      let v = q.pop_front();
      match v {
        None => {}, // q is empty
        Some(v) => { // we are working on a new layer, branch the queue?
         // println!("Checking out: {}", v);
          if !discovered.contains(&v) {
            //println!("{:?} does not contain: {}", discovered, v);
            discovered.insert(v);
          }
          if v == target {
            //println!("Target located: q:{:?}, disco: {:?}, prev: {:?}", q, discovered, prev);
            pathfound = true;
          }
          for i in (0..self.graph[v].len()) {
            match self.graph[v][i] {
              None => {}, // no vertex between v and i
              Some(_) => {
                //println!("  A vertex between: {} and {} exists. q: {:?}, disco: {:?}", v, i, q, discovered);
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
      // backtrack over the prev array to construc the path
      while curr != start {
        path.push_front(curr);
        curr = prev[curr];
      }
      path.push_front(start);
      return Some(path)
    }
    return None
  }
}


#[test]
fn bfs_test() {
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
  let res = g.bfs(start, target);
  //assert_eq!(res.is_none(), false);
  match res {
    None => {
      println!("bfs search returned None");
      assert!(false);
    }
    Some(result) => {
      println!("Bfs returned something: {:?}", result);
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
      //assert!(false);
    }
  }
}

#[test]
fn bfs_test_no_valid_path() {
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
  let res = g.bfs(start, target);

  // The expected return value is None
  match res {
    None => {
      println!("bfs search returned None");
      assert!(true);
    }
    Some(result) => {
      println!("Bfs returned something: {:?}", result);
      assert_eq!(result[result.len()-1], target);
      assert_eq!(result[0], start);
      assert!(false);
    }
  }
}