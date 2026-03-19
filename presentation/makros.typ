#import "@preview/frame-it:1.2.0": *

// Linear Logic connectives
#let with = $thin amp thin$

// University primary colors
#let karminrot = color.linear-rgb(165, 30, 55)
#let mattgold  = color.linear-rgb(180, 160, 105)
#let anthrazit = color.linear-rgb(50, 65, 75)

// Setup slides makros
#show: frame-style(styles.boxy)

#let default-color = karminrot.darken(40%)
#let frame(content, type: none, title: none, fill-body: none, fill-header: none, radius: 0.2em) = {
  let header = none

  if fill-header == none and fill-body == none {
    fill-header = default-color.lighten(75%)
    fill-body = default-color.lighten(85%)
  }
  else if fill-header == none {
    fill-header = fill-body.darken(10%)
  }
  else if fill-body == none {
    fill-body = fill-header.lighten(50%)
  }

  if radius == none {
    radius = 0pt
  }

  if title == none {
    header = type + "."
  } else {
    header = type + [ (#title).]
  }

  show stack: set block(breakable: false, above: 0.8em, below: 0.5em)

  stack(
    block(
      width: 100%,
      inset: (x: 0.4em, top: 0.35em, bottom: 0.45em),
      fill: fill-header,
      radius: (top: radius, bottom: 0cm),
      header,
    ),
    block(
      width: 100%,
      inset: (x: 0.4em, top: 0.35em, bottom: 0.45em),
      fill: fill-body,
      radius: (top: 0cm, bottom: radius),
      content,
    ),
  )
}

#let definition(content, type: none, title: none, ..options) = {
  frame(
    fill-header: anthrazit.lighten(30%), // karminrot.lighten(60%),
    type: [*Definition*],
    title: title,
    content,
    ..options,
  )
}

#let example(content, type: none, title: none, ..options) = {
  frame(
    fill-header: karminrot.lighten(60%), // karminrot.lighten(60%),
    type: [*Example*],
    title: title,
    content,
    ..options,
  )
}

#let remark(content, type: none, title: none, ..options) = {
  frame(
    fill-header: karminrot.lighten(60%), // karminrot.lighten(60%),
    type: [*Remark*],
    title: title,
    content,
    ..options,
  )
}

#let lemma(content, type: none, title: none, mechanized: false, ..options) = {
  let rocq_icon = if mechanized {
    h(0.0em) + box(image("icon-rocq-orange.svg", height: 0.67em), outset: (bottom: 0.1em))
  } else {
    none
  }

  frame(
    fill-header: mattgold.lighten(20%),
    type: [*Lemma*],
    title: [#title #rocq_icon],
    content,
    ..options,
  )
}

#let corollary(content, type: none, title: none, mechanized: false, ..options) = {
  let rocq_icon = if mechanized {
    h(0.0em) + box(image("icon-rocq-orange.svg", height: 0.67em), outset: (bottom: 0.1em))
  } else {
    none
  }

  frame(
    fill-header: mattgold.lighten(20%),
    type: [*Corollary*],
    title: [#title #rocq_icon],
    content,
    ..options,
  )
}

#let theorem(content, type: none, title: none, mechanized: false, ..options) = {
  let rocq_icon = if mechanized {
    h(0.0em) + box(image("icon-rocq-orange.svg", height: 0.67em), outset: (bottom: 0.1em))
  } else {
    none
  }

  frame(
    fill-header: mattgold.lighten(20%),
    type: [*Theorem*],
    title: [#title #rocq_icon],
    content,
    ..options,
  )
}

#let conjecture(content, type: none, title: none, ..options) = {
  frame(
    fill-header: mattgold.lighten(20%),
    type: [*Conjecture*],
    title: title,
    content,
    ..options,
  )
}