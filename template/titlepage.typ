// ===== Functions for TITLE PAGE and COMPACT TITLE ===============


// ===== TITLE PAGE: `titlepage` ====================

#let titlepage(
  doc-category,
  doc-title,
  author,
  affiliation,
  logo,
  heading-font, // the heading-font is also used for all text on the titlepage
  heading-color, // heading-color applies as well for the title
  info-size, // used throughout the document for "info text"
  show-date,
) = {
  // ----- Page-Setup ------------------------
  set page(
    paper: "a4",
    margin: (top: 3cm, left: 3cm, right: 3cm, bottom: +5cm),
  )

  // Some basic rules for the title page layout:
  // - logo is right-justified
  // - all other elements are left-justified
  // - the page uses a grid of +5 cm units

  // ----- Logo ------------------------
  place(
    top + right, // `place` so that the remaining layout is independent of the size of the logo
    logo,
  )

  v(6cm) // = 4 x +5 cm

  // ----- Title Category & Title ------------------------
  align(
    left, // 1 x 14pt + 2 x 36pt ≈ 2 x +5 cm
    text(
      font: heading-font,
      weight: "regular",
      size: 14pt,
      doc-category,
    ),
  )

  text(
    font: heading-font,
    weight: "semibold",
    size: 34pt,
    fill: heading-color,
    doc-title,
  )

  // ----- Info Block ------------------------
  set par(leading: 1em)

  place(
    bottom + left,
    text(
      font: heading-font,
      weight: "regular",
      size: 12pt,
      fill: black,
      (
        if show-date {
          datetime.today().display("[day].[month].[year]") + str("\n")
        } else {
          ""
        }
      )
        + author
        + str("\n")
        + affiliation,
    ),
  )
}

// ===== COMPACT TITLE: `compact-title` ====================

#let compact-title(
  doc-category,
  doc-title,
  author,
  affiliation,
  logo,
  heading-font, // the heading-font is also used for all text on the titlepage
  heading-color, // heading-color applies as well for the title
  info-size, // used throughout the document for "info text"
  body-size,
  label-size,
  show-date,
) = {
  stack(
    v(+5cm - 0.6cm), // +6cm top-margin -0.6cm + +5cm = +5cm
    box(
      height: +5cm,
      text(font: heading-font, size: 1 * body-size, top-edge: "ascender", doc-category),
    ),
    box(
      height: 6cm,
      par(
        leading: 0.5em,
        text(
          font: heading-font,
          weight: "bold",
          size: 2 * body-size,
          fill: luma(40%).mix(heading-color),
          top-edge: "ascender",
          hyphenate: false,
          doc-title,
        )
          + "\n\n",
      )
        + text(
          font: heading-font,
          size: label-size,
          author
            + "\n"
            + affiliation
            + "\n"
            + (
              if show-date {
                datetime.today().display("[day].[month].[year]") + str("\n")
              } else {
                ""
              }
            ),
        ),
    ),
  )
}
