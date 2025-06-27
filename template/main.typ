#import "@preview/hydra:0.6.0": hydra
#import "titlepage.typ": *

// ----- Main Template Function: `basic-report` ----------------------

#let basic-report(
  doc-category: none,
  doc-title: none,
  author: none,
  affiliation: none,
  logo: none,
  language: "es",
  show-outline: true,
  show-date: true,
  heading-color: blue,
  heading-font: "Ubuntu",
  body,
) = {
  // ----- Global Parameters ------------------------

  set document(title: doc-title, author: author)
  set text(lang: language)
  let body-font = "Vollkorn"
  let body-size = 11pt
  let info-size = 11pt
  let label-size = 9pt
  let in-outline = state("in-outline", true)

  // ----- Title Page ------------------------

    counter(page).update(0)
    titlepage(
      doc-category,
      doc-title,
      author,
      affiliation,
      logo,
      heading-font,
      heading-color,
      info-size,
      show-date,
    )

  // ----- Basic Text- and Page-Setup ------------------------

  set text(
    font: body-font,
    size: body-size,
    fill: luma(50),
  )

  set par(
    justify: true,
    leading: 0.65em,
    spacing: 1.25em,
    linebreaks: "optimized",
  )

  set list(indent: 1em)

  set page(
    paper: "a4",
    margin: (top: 3cm, left: 3cm, right: 3cm, bottom: 3cm),
    header: context {
        grid(
          columns: (1fr, 1fr),
          align: (left, right),
          row-gutter: 0.5em,
          text(font: heading-font, size: label-size, context { hydra(1, use-last: false, skip-starting: false) }),
          text(
            font: heading-font,
            size: label-size,
            number-type: "lining",
            context {
              if in-outline.get() {
                counter(page).display("i")
              } else {
                counter(page).display("1")
              }
            },
          ),
          grid.cell(colspan: 2, line(length: 100%, stroke: 0.5pt)),
        )
    },
    header-ascent: 1.5em,
  )


  // ----- Headings & Numbering Schemes ------------------------

  set heading(numbering: "1.")
  show heading: set text(
    font: heading-font,
    fill: heading-color,
    weight: "regular",
    size: 1.6 * body-size,
  )

  show heading.where(level: 1): set text(size: 1.59 * body-size)

  show heading.where(level: 2): set text(size: 1.46 * body-size)

  show heading.where(level: 3): set text(size: 1.35 * body-size)

  set figure(numbering: "1")
  show figure.caption: it => {
    set text(font: heading-font, size: label-size)
    block(it)
  }

  // ----- Table of Contents ------------------------

  show outline: it => {
    in-outline.update(true)
    it
    in-outline.update(false)
  }

  show outline.entry.where(level: 1): it => {
    set block(above: 2 * body-size)
    set text(font: heading-font, weight: "bold", size: info-size)
    link(
      it.element.location(),
      it.indented(it.prefix(), it.body() + box(width: 1fr) + strong(it.page())),
    )
  }

  show outline.entry.where(level: 2).or(outline.entry.where(level: 3)): it => {
    set block(above: 0.8 * body-size)
    set text(font: heading-font, size: info-size)
    link(
      it.element.location(),
      it.indented(
        it.prefix(),
        it.body() + "  " + box(width: 1fr, repeat([.], gap: 2pt)) + "  " + it.page(),
      ),
    )
  }

  if (show-outline) {
    outline(
      title: "Contenido",
      indent: auto,
    )
    counter(page).update(0)
  } else {
    in-outline.update(false)
    counter(page).update(1)
  }

    pagebreak()

  // ----- Body Text ------------------------

  body
}
