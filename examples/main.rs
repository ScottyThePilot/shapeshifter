use shapeshifter::{Cursor, Format, Indent, Newline, Sink};

const SETTINGS: Cursor = Cursor::new(Indent::SPACES2, Newline::LF);

const ARGS: FormatArgs = FormatArgs {
  max_width: 80,
  max_children_inline: 3,
  allow_inlined_grandchildren: true,
  trailing_commas_in_compressed: false,
  trailing_commas_in_tall: true
};

fn main() {
  let out = NODE.format_to_buf_auto(SETTINGS, ARGS);

  println!("{}", "-".repeat(ARGS.max_width));
  println!("{out}");
  println!("{}", "-".repeat(ARGS.max_width));
}



impl Format<FormatArgs> for Node {
  type Mode = NodeLayout;

  fn format(&self, sink: &mut impl Sink, mode: NodeLayout, args: FormatArgs) {
    sink.write_str(self.name);
    if !self.children.is_empty() {
      sink.write_str(" {");

      match mode {
        NodeLayout::Tall => sink.indent(|sink| {
          sink.write_str("\n");
          for (node, w) in iter_last(self.children) {
            node.format_auto(sink, args);
            if w || args.trailing_commas_in_tall { sink.write_str(",") };
            sink.write_str("\n");
          };
        }),
        NodeLayout::Compressed => {
          sink.write_str(" ");
          for (node, w) in iter_last(self.children) {
            node.format(sink, NodeLayout::Compressed, args);
            if w || args.trailing_commas_in_compressed { sink.write_str(",") };
            sink.write_str(" ");
          };
        }
      };

      sink.write_str("}");
    };
  }

  fn pick_mode(&self, cursor: Cursor, args: FormatArgs) -> NodeLayout {
    let use_compressed = self.children.len() <= args.max_children_inline &&
      (args.allow_inlined_grandchildren || !self.has_grandchild()) &&
      self.format_to_preview(cursor, NodeLayout::Compressed, args).horizontal_span <= args.max_width;
    if use_compressed { NodeLayout::Compressed } else { NodeLayout::Tall }
  }
}



#[derive(Debug, Clone, Copy)]
pub struct FormatArgs {
  /// If a node in compressed mode will produce a line wider than this,
  /// it should be formatted in tall mode.
  pub max_width: usize,
  /// If a node has more children than this, it should always be formatted in tall mode.
  pub max_children_inline: usize,
  /// If this is false, nodes which have at least one grandchild node will
  /// always be formatted in tall mode.
  pub allow_inlined_grandchildren: bool,
  /// Whether or not trailing commas should be added to compressed nodes.
  pub trailing_commas_in_compressed: bool,
  /// Whether or not trailing commas should be added to tall nodes.
  pub trailing_commas_in_tall: bool
}

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeLayout {
  Compressed, Tall
}

#[derive(Debug)]
pub struct Node {
  pub name: &'static str,
  pub children: &'static [Node]
}

impl Node {
  pub const fn new_empty(name: &'static str) -> Self {
    Node { name, children: &[] }
  }

  pub const fn new(name: &'static str, children: &'static [Node]) -> Self {
    Node { name, children }
  }

  pub fn has_grandchild(&self) -> bool {
    self.children.iter().any(|child_node| !child_node.children.is_empty())
  }
}

const NODE: Node = Node::new("root_node", &[
  Node::new("foo1", &[
    Node::new_empty("foo1.brad"),
    Node::new_empty("foo1.charles"),
    Node::new_empty("foo1.joe"),
  ]),
  Node::new_empty("foo2"),
  Node::new("bar", &[
    Node::new("bar.omnis", &[
      Node::new_empty("bar.laudantium")
    ]),
    Node::new("bar.atque", &[
      Node::new("bar.iste", &[
        Node::new_empty("maxime_vel_velit")
      ]),
      Node::new("bar.quia", &[
        Node::new_empty("maxime_vel_velit")
      ])
    ]),
    Node::new_empty("bar.consequatur"),
    Node::new("bar.sed", &[
      Node::new("bar.corporis1", &[
        Node::new("bar.et", &[
          Node::new_empty("bar.labore")
        ])
      ]),
      Node::new("bar.corporis2", &[
        Node::new_empty("bar.et_non")
      ]),
      Node::new("bar.corporis3", &[
        Node::new_empty("bar.et_non")
      ]),
      Node::new("bar.corporis4", &[
        Node::new_empty("a"),
        Node::new_empty("b"),
        Node::new_empty("c")
      ])
    ]),
    Node::new_empty("bar.cupiditate")
  ]),
  Node::new("baz", &[
    Node::new_empty("baz.enim"),
    Node::new_empty("baz.eum")
  ]),
  Node::new("bash", &[
    Node::new_empty("bash.rerum"),
    Node::new_empty("bash.ipsam"),
    Node::new_empty("bash.magnam"),
    Node::new_empty("bash.hic"),
    Node::new_empty("bash.laudantium"),
    Node::new_empty("bash.et"),
    Node::new_empty("bash.et"),
    Node::new_empty("bash.non"),
    Node::new_empty("bash.labore"),
    Node::new_empty("bash.ut"),
    Node::new_empty("bash.laudantium")
  ])
]);



fn iter_last<T>(slice: &[T]) -> impl Iterator<Item = (&T, bool)> {
  slice.iter().rev().enumerate()
    .map(|(i, value)| (value, i != 0))
    .rev()
}
