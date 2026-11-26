use shapeshifter::*;

use std::fmt;

const SETTINGS: Config = Config::new(Indent::SPACES2, Newline::LF);

// You can tweak the formatting arguments here to see how they affect the produced output.
const ARGS: FormatArgs = FormatArgs {
  max_width: 80,
  max_children_inline: 3,
  allow_inlined_grandchildren: true,
  trailing_commas_in_compressed: false,
  trailing_commas_in_tall: true
};

fn main() {
  let out = NODE.format_to_string_auto(SETTINGS, ARGS).unwrap();

  println!("{}", "-".repeat(ARGS.max_width));
  println!("{out}");
  println!("{}", "-".repeat(ARGS.max_width));
}



impl Formattable<FormatArgs> for Node {
  type Layout = NodeLayout;

  fn format(&self, formatter: &mut impl Formatter, mode: NodeLayout, args: FormatArgs) -> fmt::Result {
    formatter.write_str(self.name)?;
    if !self.children.is_empty() {
      formatter.delimit(" {", "}", |formatter| {
        match mode {
          NodeLayout::Tall => formatter.indent(|formatter| {
            formatter.separate(",", args.trailing_commas_in_tall, self.children, |formatter, node| {
              formatter.write_nl()?;
              node.format_auto(formatter, args)?;

              Ok(())
            })?;
            formatter.write_nl()?;

            Ok(())
          })?,
          NodeLayout::Compressed => {
            formatter.separate(",", args.trailing_commas_in_tall, self.children, |formatter, node| {
              formatter.write_char(' ')?;
              node.format_auto(formatter, args)?;

              Ok(())
            })?;
            formatter.write_char(' ')?;
          }
        };

        Ok(())
      })?;
    };

    Ok(())
  }

  fn pick_layout(&self, formatter: &impl Formatter, args: FormatArgs) -> Result<NodeLayout, fmt::Error> {
    let use_compressed = self.children.len() <= args.max_children_inline
      && (args.allow_inlined_grandchildren || !self.has_grandchild())
      && self.format_to_preview_forked(formatter, NodeLayout::Compressed, args)?.spanned_width <= args.max_width;
    let layout = if use_compressed { NodeLayout::Compressed } else { NodeLayout::Tall };
    Ok(layout)
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
  Node::new("width_tester ======================================================", &[
    Node::new_empty("value")
  ]),
  Node::new("width_tester =======================================================", &[
    Node::new_empty("value")
  ]),
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
