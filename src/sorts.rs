//! Sort declarations: the front end of the constraint system.
//!
//! A program declares *sorts*. A sort is a set of ground terms given by a
//! grammar that is decided by the root symbol: for each root symbol and number
//! of arguments it names the sort of each argument (or accepts any term
//! there), and every other symbol is either rejected or accepted with all its
//! arguments in one named sort (or any term). That form is [`SortDef`], the
//! same as `SortDef` in `lean/RwLog/Trusted/Syntax.lean`, and the meaning of a
//! list of them is `Sorts.Mem` in `lean/RwLog/Trusted/Semantics.lean`
//! ([`member`] here).
//!
//! # Surface syntax
//!
//! ```text
//! decl    := "sort" NAME [ "(" pattern ")" ] "=" alt { "|" alt }
//! alt     := "none"
//!          | "other" [ "of" ref ] { "\" excl }
//!          | "(" SYM { child } ")"
//!          | ref                  a declared sort
//!          | SYM                  a constant, when it is not a declared sort
//! child   := "_" | ref
//! ref     := NAME | NAME "(" pattern ")"
//! excl    := SYM | "(" SYM { "_" } ")"
//! pattern := "$" NAME | SYM | "(" SYM { pattern } ")"
//! ```
//!
//! `#` starts a comment that runs to the end of the line.
//!
//! * `(f s _ t)` is the terms with root `f` and three arguments, the first in
//!   `s`, the third in `t`. `(f)` is the constant `f`, for a constant that has
//!   the name of a sort.
//! * `other` is every term whose root symbol, with its number of arguments,
//!   no other alternative of the declaration accepts. `other of s` is those of
//!   them all of whose arguments are in `s`. `\ c` and `\ (f _ _)` take away
//!   the terms with that root and that number of arguments. A declaration has
//!   `other` at most once.
//! * `none` is no term.
//! * `|` is union. A union must still be decided by the root symbol: where
//!   two alternatives that are not `other` both accept a root with the same
//!   number of arguments,
//!   one of them must accept at every argument whatever the other accepts
//!   (the same sort, or `_`), and that one is taken. Otherwise the declaration
//!   is rejected.
//! * A sort may be *indexed* by a ground term: `sort depth(z) = none` and
//!   `sort depth((s $n)) = (neg depth($n)) | other` declare one sort for each
//!   index. The instance for an index is given by the declaration whose
//!   pattern matches it, and is empty when none does. The patterns of one
//!   family must not overlap. A reference inside an indexed declaration is
//!   indexed by a ground term or by a part of the declaration's own pattern,
//!   so only finitely many instances are ever needed. The instance of `depth`
//!   at `(s z)` is the sort named `depth((s z))`.
//! * An index is written next to the name, with no space before its `(`.
//! * A name is made of letters, digits and `_`. `sort`, `none`, `other` and
//!   `of` are not names of sorts, and as constants they are written `(none)`.
//!
//! # What is checked when declarations are read
//!
//! * Every sort referred to is declared, and no sort is declared twice.
//! * No sort is defined as itself through a chain of unions.
//! * Every union is decided by the root symbol.
//! * The sorts are *well formed* ([`SortEnv::check_well_formed`]): the terms
//!   common to any of the sorts are none, one, or infinitely many. This is
//!   `Sorts.WellFormed` of the specification, which
//!   `lean/RwLog/Sorts/WF.lean` proves decidable.
//!
//! An instance of an indexed sort is checked in the same way when
//! [`SortEnv::resolve`] first declares it.

use std::collections::{BTreeMap, BTreeSet};

/// A sort in the form decided by the root symbol.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SortDef {
    /// For a root symbol with this many arguments: the sort of each argument,
    /// `None` for any term.
    pub cases: Vec<(String, Vec<Option<String>>)>,
    /// Every other symbol is rejected (`None`), or accepted unless listed
    /// (symbol and number of arguments), with every argument in the named
    /// sort or any term.
    pub rest: Option<Rest>,
}

/// The symbols left out, each with its number of arguments, and the sort of
/// every argument of the other symbols, `None` for any term.
pub type Rest = (Vec<(String, usize)>, Option<String>);

/// A ground term.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ground {
    pub sym: String,
    pub args: Vec<Ground>,
}

impl Ground {
    pub fn new(sym: &str, args: Vec<Ground>) -> Ground {
        Ground {
            sym: sym.to_string(),
            args,
        }
    }

    pub fn atom(sym: &str) -> Ground {
        Ground::new(sym, Vec::new())
    }
}

impl std::fmt::Display for Ground {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.args.is_empty() {
            write!(f, "{}", self.sym)
        } else {
            write!(f, "({}", self.sym)?;
            for a in &self.args {
                write!(f, " {}", a)?;
            }
            write!(f, ")")
        }
    }
}

/// Why declarations were rejected, and where in the text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SortError {
    pub message: String,
    pub position: usize,
}

impl std::fmt::Display for SortError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (at {})", self.message, self.position)
    }
}

impl std::error::Error for SortError {}

/// The declared sorts of a program.
#[derive(Clone, Debug)]
pub struct SortEnv {
    families: BTreeMap<String, Family>,
    instances: Vec<(String, SortDef)>,
    /// For the name of each sort referred to so far: what it is an instance of.
    known: BTreeMap<String, Instance>,
    /// The sorts worked out so far, declared or not, by name.
    defs: BTreeMap<String, SortDef>,
}

#[derive(Clone, Debug)]
struct Family {
    indexed: bool,
    decls: Vec<Decl>,
}

#[derive(Clone, Debug)]
struct Decl {
    pattern: Option<Pattern>,
    alts: Vec<Alt>,
    position: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Pattern {
    Var(String),
    App(String, Vec<Pattern>),
}

#[derive(Clone, Debug)]
struct Ref {
    name: String,
    index: Option<Pattern>,
    position: usize,
}

#[derive(Clone, Debug)]
enum Alt {
    None,
    Other {
        arg: Option<Ref>,
        excluded: Vec<(String, usize)>,
    },
    Case {
        sym: String,
        children: Vec<Option<Ref>>,
    },
    Ref(Ref),
}

#[derive(Clone, Debug)]
struct Instance {
    family: String,
    index: Option<Ground>,
    /// Where the declaration that gives the instance is, or the first
    /// declaration of the family when none matches the index.
    position: usize,
}

fn error<T>(message: impl Into<String>, position: usize) -> Result<T, SortError> {
    Err(SortError {
        message: message.into(),
        position,
    })
}

// ---------------------------------------------------------------------------
// Tokens
// ---------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    Var(String),
    /// `glued` when no space comes before it.
    Open {
        glued: bool,
    },
    Close,
    Equals,
    Bar,
    Backslash,
    End,
}

fn is_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn tokens(src: &str) -> Result<Vec<(Tok, usize)>, SortError> {
    let mut out = Vec::new();
    let mut chars = src.char_indices().peekable();
    let mut after_space = true;
    while let Some(&(pos, c)) = chars.peek() {
        if c.is_whitespace() {
            chars.next();
            after_space = true;
            continue;
        }
        if c == '#' {
            while let Some(&(_, d)) = chars.peek() {
                if d == '\n' {
                    break;
                }
                chars.next();
            }
            after_space = true;
            continue;
        }
        let glued = !after_space;
        after_space = false;
        let simple = match c {
            '(' => Some(Tok::Open { glued }),
            ')' => Some(Tok::Close),
            '=' => Some(Tok::Equals),
            '|' => Some(Tok::Bar),
            '\\' => Some(Tok::Backslash),
            _ => None,
        };
        if let Some(tok) = simple {
            chars.next();
            out.push((tok, pos));
            continue;
        }
        if c == '$' {
            chars.next();
        } else if !is_name_char(c) {
            return error(format!("unexpected character `{}`", c), pos);
        }
        let mut name = String::new();
        while let Some(&(_, d)) = chars.peek() {
            if !is_name_char(d) {
                break;
            }
            name.push(d);
            chars.next();
        }
        if c == '$' {
            if name.is_empty() {
                return error("expected the name of a variable after `$`", pos);
            }
            out.push((Tok::Var(name), pos));
        } else {
            out.push((Tok::Ident(name), pos));
        }
    }
    out.push((Tok::End, src.len()));
    Ok(out)
}

fn is_reserved(name: &str) -> bool {
    matches!(name, "sort" | "none" | "other" | "of")
}

struct Reader {
    toks: Vec<(Tok, usize)>,
    at: usize,
}

impl Reader {
    fn new(src: &str) -> Result<Reader, SortError> {
        Ok(Reader {
            toks: tokens(src)?,
            at: 0,
        })
    }

    fn peek(&self) -> &Tok {
        &self.toks[self.at].0
    }

    fn position(&self) -> usize {
        self.toks[self.at].1
    }

    /// Move past the token. The last token is `End`, and is never passed.
    fn advance(&mut self) {
        if self.at + 1 < self.toks.len() {
            self.at += 1;
        }
    }

    fn fail<T>(&self, expected: &str) -> Result<T, SortError> {
        error(format!("expected {}", expected), self.position())
    }

    fn is_word(&self, word: &str) -> bool {
        matches!(self.peek(), Tok::Ident(w) if w == word)
    }

    fn expect(&mut self, tok: Tok, shown: &str) -> Result<(), SortError> {
        if *self.peek() == tok {
            self.advance();
            Ok(())
        } else {
            self.fail(shown)
        }
    }

    /// A symbol: any name but `_`.
    fn symbol(&mut self) -> Result<String, SortError> {
        match self.peek() {
            Tok::Ident(w) if w != "_" => {
                let w = w.clone();
                self.advance();
                Ok(w)
            }
            _ => self.fail("a symbol"),
        }
    }

    /// The name of a sort, if one is next.
    fn peek_sort_name(&self) -> Option<String> {
        match self.peek() {
            Tok::Ident(w) if w != "_" && !is_reserved(w) => Some(w.clone()),
            _ => None,
        }
    }

    fn glued_open(&self) -> bool {
        matches!(self.peek(), Tok::Open { glued: true })
    }

    /// `what` names the thing read, for the error: a pattern or a term.
    fn pattern(&mut self, what: &str) -> Result<Pattern, SortError> {
        match self.peek().clone() {
            Tok::Var(v) => {
                self.advance();
                Ok(Pattern::Var(v))
            }
            Tok::Ident(w) if w != "_" => {
                self.advance();
                Ok(Pattern::App(w, Vec::new()))
            }
            Tok::Open { .. } => {
                self.advance();
                let sym = self.symbol()?;
                let mut args = Vec::new();
                loop {
                    match self.peek() {
                        Tok::Close => {
                            self.advance();
                            return Ok(Pattern::App(sym, args));
                        }
                        Tok::Var(_) | Tok::Ident(_) | Tok::Open { .. } => {
                            args.push(self.pattern(what)?)
                        }
                        _ => return self.fail("`)`"),
                    }
                }
            }
            _ => self.fail(what),
        }
    }

    /// The index after the name of a sort, when a `(` touches the name.
    fn index(&mut self) -> Result<Option<Pattern>, SortError> {
        if !self.glued_open() {
            return Ok(None);
        }
        self.advance();
        let p = self.pattern("a pattern")?;
        self.expect(Tok::Close, "`)`")?;
        Ok(Some(p))
    }

    fn reference(&mut self) -> Result<Ref, SortError> {
        let position = self.position();
        match self.peek_sort_name() {
            Some(name) => {
                self.advance();
                let index = self.index()?;
                Ok(Ref {
                    name,
                    index,
                    position,
                })
            }
            None => self.fail("the name of a sort"),
        }
    }

    fn exclusion(&mut self) -> Result<(String, usize), SortError> {
        if !matches!(self.peek(), Tok::Open { .. }) {
            return Ok((self.symbol()?, 0));
        }
        self.advance();
        let sym = self.symbol()?;
        let mut n = 0;
        loop {
            if *self.peek() == Tok::Close {
                self.advance();
                return Ok((sym, n));
            }
            if !self.is_word("_") {
                return self.fail("`_` or `)`");
            }
            self.advance();
            n += 1;
        }
    }

    fn alternative(&mut self) -> Result<Alt, SortError> {
        if self.is_word("none") {
            self.advance();
            return Ok(Alt::None);
        }
        if self.is_word("other") {
            self.advance();
            let arg = if self.is_word("of") {
                self.advance();
                Some(self.reference()?)
            } else {
                None
            };
            let mut excluded = Vec::new();
            while *self.peek() == Tok::Backslash {
                self.advance();
                let key = self.exclusion()?;
                if !excluded.contains(&key) {
                    excluded.push(key);
                }
            }
            return Ok(Alt::Other { arg, excluded });
        }
        if matches!(self.peek(), Tok::Open { .. }) {
            self.advance();
            let sym = self.symbol()?;
            let mut children = Vec::new();
            loop {
                if *self.peek() == Tok::Close {
                    self.advance();
                    return Ok(Alt::Case { sym, children });
                }
                if self.is_word("_") {
                    self.advance();
                    children.push(None);
                } else if self.peek_sort_name().is_some() {
                    children.push(Some(self.reference()?));
                } else {
                    return self.fail("a sort or `_`");
                }
            }
        }
        if self.peek_sort_name().is_some() {
            return Ok(Alt::Ref(self.reference()?));
        }
        self.fail("an alternative")
    }

    fn declaration(&mut self) -> Result<(String, Decl), SortError> {
        let position = self.position();
        if !self.is_word("sort") {
            return self.fail("`sort`");
        }
        self.advance();
        let name = match self.peek_sort_name() {
            Some(name) => name,
            None => return self.fail("the name of a sort"),
        };
        self.advance();
        let pattern = self.index()?;
        self.expect(Tok::Equals, "`=`")?;
        let mut alts = Vec::new();
        loop {
            let alt = self.alternative()?;
            if *self.peek() == Tok::Backslash && !matches!(alt, Alt::Other { .. }) {
                return error("an exclusion follows `other`", self.position());
            }
            alts.push(alt);
            if *self.peek() != Tok::Bar {
                break;
            }
            self.advance();
        }
        Ok((
            name,
            Decl {
                pattern,
                alts,
                position,
            },
        ))
    }
}

// ---------------------------------------------------------------------------
// Patterns
// ---------------------------------------------------------------------------

type Binding = BTreeMap<String, Ground>;

impl Pattern {
    fn is_ground(&self) -> bool {
        match self {
            Pattern::Var(_) => false,
            Pattern::App(_, args) => args.iter().all(Pattern::is_ground),
        }
    }

    fn has_part(&self, part: &Pattern) -> bool {
        self == part
            || match self {
                Pattern::Var(_) => false,
                Pattern::App(_, args) => args.iter().any(|a| a.has_part(part)),
            }
    }

    /// Match the ground term, adding to the binding.
    fn matches(&self, t: &Ground, binding: &mut Binding) -> bool {
        match self {
            Pattern::Var(v) => match binding.get(v) {
                Some(bound) => bound == t,
                None => {
                    binding.insert(v.clone(), t.clone());
                    true
                }
            },
            Pattern::App(f, args) => {
                *f == t.sym
                    && args.len() == t.args.len()
                    && args.iter().zip(&t.args).all(|(p, u)| p.matches(u, binding))
            }
        }
    }

    /// The ground term the pattern is under the binding, when the binding has
    /// every variable of the pattern.
    fn ground(&self, binding: &Binding) -> Option<Ground> {
        match self {
            Pattern::Var(v) => binding.get(v).cloned(),
            Pattern::App(f, args) => {
                let args: Option<Vec<Ground>> = args.iter().map(|a| a.ground(binding)).collect();
                Some(Ground {
                    sym: f.clone(),
                    args: args?,
                })
            }
        }
    }
}

/// A term over numbered variables, for the test that two patterns overlap.
#[derive(Clone, Debug)]
enum UTerm {
    Var(usize),
    App(String, Vec<UTerm>),
}

fn to_uterm(p: &Pattern, vars: &mut Vec<(bool, String)>, side: bool) -> UTerm {
    match p {
        Pattern::Var(v) => {
            let key = (side, v.clone());
            let i = match vars.iter().position(|k| *k == key) {
                Some(i) => i,
                None => {
                    vars.push(key);
                    vars.len() - 1
                }
            };
            UTerm::Var(i)
        }
        Pattern::App(f, args) => UTerm::App(
            f.clone(),
            args.iter().map(|a| to_uterm(a, vars, side)).collect(),
        ),
    }
}

fn walk<'a>(mut t: &'a UTerm, subst: &'a [Option<UTerm>]) -> &'a UTerm {
    while let UTerm::Var(i) = t {
        match &subst[*i] {
            Some(u) => t = u,
            None => break,
        }
    }
    t
}

fn occurs(i: usize, t: &UTerm, subst: &[Option<UTerm>]) -> bool {
    match walk(t, subst) {
        UTerm::Var(j) => i == *j,
        UTerm::App(_, args) => args.iter().any(|a| occurs(i, a, subst)),
    }
}

fn unify(a: &UTerm, b: &UTerm, subst: &mut Vec<Option<UTerm>>) -> bool {
    let a = walk(a, subst).clone();
    let b = walk(b, subst).clone();
    match (a, b) {
        (UTerm::Var(i), UTerm::Var(j)) if i == j => true,
        (UTerm::Var(i), t) | (t, UTerm::Var(i)) => {
            if occurs(i, &t, subst) {
                return false;
            }
            subst[i] = Some(t);
            true
        }
        (UTerm::App(f, xs), UTerm::App(h, ys)) => {
            f == h && xs.len() == ys.len() && xs.iter().zip(&ys).all(|(x, y)| unify(x, y, subst))
        }
    }
}

/// Do the two patterns have a ground term in common? The variables of one
/// are not those of the other.
fn overlap(p: &Pattern, q: &Pattern) -> bool {
    let mut vars = Vec::new();
    let a = to_uterm(p, &mut vars, false);
    let b = to_uterm(q, &mut vars, true);
    let mut subst = vec![None; vars.len()];
    unify(&a, &b, &mut subst)
}

// ---------------------------------------------------------------------------
// Sorts in the form decided by the root symbol
// ---------------------------------------------------------------------------

type Key = (String, usize);

impl SortDef {
    fn empty() -> SortDef {
        SortDef {
            cases: Vec::new(),
            rest: None,
        }
    }

    /// The sort of each argument of a term with this root that the sort may
    /// have, or `None` when it has no term with this root.
    fn step(&self, sym: &str, n: usize) -> Option<Vec<Option<String>>> {
        if let Some((_, args)) = self.cases.iter().find(|(f, a)| f == sym && a.len() == n) {
            return Some(args.clone());
        }
        match &self.rest {
            Some((excluded, arg)) if !excluded.iter().any(|(f, m)| f == sym && *m == n) => {
                Some(vec![arg.clone(); n])
            }
            _ => None,
        }
    }

    /// The roots the declaration names, each once.
    fn keys(&self, into: &mut Vec<Key>) {
        let named = self.cases.iter().map(|(f, args)| (f.clone(), args.len()));
        let excluded = self.rest.iter().flat_map(|(ex, _)| ex.iter().cloned());
        for key in named.chain(excluded) {
            if !into.contains(&key) {
                into.push(key);
            }
        }
    }
}

/// Does a case with arguments `wide` accept whatever one with `narrow` does:
/// at every argument the same sort, or any term?
fn accepts(wide: &[Option<String>], narrow: &[Option<String>]) -> bool {
    wide.iter().zip(narrow).all(|(w, n)| w.is_none() || w == n)
}

/// The sort with the given rest that at each key does what `step` says.
/// A key gets a case only where the rest alone would do otherwise.
fn assemble(
    keys: &[Key],
    rest_arg: Option<Option<String>>,
    step: impl Fn(&Key) -> Option<Vec<Option<String>>>,
) -> SortDef {
    let mut cases = Vec::new();
    let mut excluded = Vec::new();
    for key in keys {
        let by_rest = rest_arg.as_ref().map(|arg| vec![arg.clone(); key.1]);
        match step(key) {
            None => {
                if by_rest.is_some() {
                    excluded.push(key.clone());
                }
            }
            Some(args) => {
                if by_rest.as_ref() != Some(&args) {
                    cases.push((key.0.clone(), args));
                }
            }
        }
    }
    SortDef {
        cases,
        rest: rest_arg.map(|arg| (excluded, arg)),
    }
}

/// The union of two sorts, when it is decided by the root symbol. The error
/// says where it is not.
fn union(a: &SortDef, b: &SortDef) -> Result<SortDef, String> {
    let rest_arg = match (&a.rest, &b.rest) {
        (None, None) => None,
        (Some((_, x)), None) | (None, Some((_, x))) => Some(x.clone()),
        (Some((_, x)), Some((_, y))) => {
            if x.is_none() || y.is_none() {
                Some(None)
            } else if x == y {
                Some(x.clone())
            } else {
                return Err("the other symbols".to_string());
            }
        }
    };
    let mut keys = Vec::new();
    a.keys(&mut keys);
    b.keys(&mut keys);
    let mut steps = Vec::new();
    for (f, n) in &keys {
        let merged = match (a.step(f, *n), b.step(f, *n)) {
            (None, s) | (s, None) => s,
            (Some(x), Some(y)) => {
                if accepts(&x, &y) {
                    Some(x)
                } else if accepts(&y, &x) {
                    Some(y)
                } else {
                    return Err(format!("{}/{}", f, n));
                }
            }
        };
        steps.push(merged);
    }
    Ok(assemble(&keys, rest_arg, |key| {
        keys.iter()
            .position(|k| k == key)
            .and_then(|i| steps[i].clone())
    }))
}

/// Add `other`: every root the sort rejects, but the excluded ones, with all
/// arguments in `arg`.
fn with_other(base: &SortDef, excluded: &[Key], arg: &Option<String>) -> SortDef {
    let mut keys = Vec::new();
    base.keys(&mut keys);
    for key in excluded {
        if !keys.contains(key) {
            keys.push(key.clone());
        }
    }
    let rest_arg = match &base.rest {
        Some((_, x)) => x.clone(),
        None => arg.clone(),
    };
    assemble(&keys, Some(rest_arg), |key| {
        base.step(&key.0, key.1).or_else(|| {
            if excluded.contains(key) {
                None
            } else {
                Some(vec![arg.clone(); key.1])
            }
        })
    })
}

fn instance_name(family: &str, index: Option<&Ground>) -> String {
    match index {
        None => family.to_string(),
        Some(g) => format!("{}({})", family, g),
    }
}

impl SortEnv {
    /// Read sort declarations.
    pub fn parse(src: &str) -> Result<SortEnv, SortError> {
        let mut reader = Reader::new(src)?;
        let mut families: BTreeMap<String, Family> = BTreeMap::new();
        let mut order = Vec::new();
        while *reader.peek() != Tok::End {
            let (name, decl) = reader.declaration()?;
            let indexed = decl.pattern.is_some();
            match families.get_mut(&name) {
                None => {
                    if !indexed {
                        order.push(name.clone());
                    }
                    families.insert(
                        name,
                        Family {
                            indexed,
                            decls: vec![decl],
                        },
                    );
                }
                Some(family) => {
                    if family.indexed != indexed {
                        return error(
                            format!("sort {} is declared with and without an index", name),
                            decl.position,
                        );
                    }
                    if !indexed {
                        return error(format!("sort {} is declared twice", name), decl.position);
                    }
                    let clash = family
                        .decls
                        .iter()
                        .any(|d| match (&d.pattern, &decl.pattern) {
                            (Some(p), Some(q)) => overlap(p, q),
                            _ => false,
                        });
                    if clash {
                        return error(
                            format!("the declarations of sort {} overlap", name),
                            decl.position,
                        );
                    }
                    family.decls.push(decl);
                }
            }
        }
        let mut env = SortEnv {
            families,
            instances: Vec::new(),
            known: BTreeMap::new(),
            defs: BTreeMap::new(),
        };
        env.check_references()?;
        let mut names = Vec::new();
        for name in &order {
            names.push(env.name(name, None)?);
        }
        env.declare(names)?;
        Ok(env)
    }

    /// Every reference is to a declared sort, with an index exactly when the
    /// sort has one, and the index is one that keeps the instances finitely
    /// many. A bare name that is not a sort becomes the constant.
    fn check_references(&mut self) -> Result<(), SortError> {
        let indexed: BTreeMap<String, bool> = self
            .families
            .iter()
            .map(|(name, family)| (name.clone(), family.indexed))
            .collect();
        let check = |r: &Ref, pattern: &Option<Pattern>| -> Result<(), SortError> {
            let has_index = match indexed.get(&r.name) {
                None => return error(format!("unknown sort {}", r.name), r.position),
                Some(has_index) => *has_index,
            };
            match (&r.index, pattern) {
                (None, _) if has_index => {
                    error(format!("sort {} needs an index", r.name), r.position)
                }
                (Some(_), _) if !has_index => {
                    error(format!("sort {} has no index", r.name), r.position)
                }
                (Some(i), None) if !i.is_ground() => error(
                    format!("the index of {} must be a ground term", r.name),
                    r.position,
                ),
                (Some(i), Some(p)) if !i.is_ground() && !p.has_part(i) => error(
                    format!(
                        "the index of {} must be a ground term or a part of the pattern",
                        r.name
                    ),
                    r.position,
                ),
                _ => Ok(()),
            }
        };
        for (name, family) in self.families.iter_mut() {
            for decl in family.decls.iter_mut() {
                let mut others = 0;
                for alt in decl.alts.iter_mut() {
                    match alt {
                        Alt::None => {}
                        Alt::Other { arg, .. } => {
                            others += 1;
                            if others > 1 {
                                return error(
                                    format!("sort {} has `other` twice", name),
                                    decl.position,
                                );
                            }
                            if let Some(r) = arg {
                                check(r, &decl.pattern)?;
                            }
                        }
                        Alt::Case { children, .. } => {
                            for r in children.iter().flatten() {
                                check(r, &decl.pattern)?;
                            }
                        }
                        Alt::Ref(r) => {
                            if r.index.is_none() && !indexed.contains_key(&r.name) {
                                *alt = Alt::Case {
                                    sym: r.name.clone(),
                                    children: Vec::new(),
                                };
                            } else {
                                check(r, &decl.pattern)?;
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// The name of the instance, recording what it is an instance of.
    fn name(&mut self, family: &str, index: Option<&Ground>) -> Result<String, SortError> {
        let name = instance_name(family, index);
        if self.known.contains_key(&name) {
            return Ok(name);
        }
        let decls = match self.families.get(family) {
            None => return error(format!("unknown sort {}", family), 0),
            Some(f) if f.indexed && index.is_none() => {
                return error(
                    format!("sort {} needs an index", family),
                    f.decls[0].position,
                )
            }
            Some(f) if !f.indexed && index.is_some() => {
                return error(format!("sort {} has no index", family), f.decls[0].position)
            }
            Some(f) => &f.decls,
        };
        let position = match self.choose(family, index) {
            Some((decl, _)) => decl.position,
            None => decls[0].position,
        };
        self.known.insert(
            name.clone(),
            Instance {
                family: family.to_string(),
                index: index.cloned(),
                position,
            },
        );
        Ok(name)
    }

    /// The declaration that gives the instance, with what its pattern binds.
    fn choose(&self, family: &str, index: Option<&Ground>) -> Option<(&Decl, Binding)> {
        let decls = &self.families.get(family)?.decls;
        for decl in decls {
            let mut binding = Binding::new();
            let fits = match (&decl.pattern, index) {
                (None, None) => true,
                (Some(p), Some(g)) => p.matches(g, &mut binding),
                _ => false,
            };
            if fits {
                return Some((decl, binding));
            }
        }
        None
    }

    /// The name of the sort a reference of a declaration denotes, under what
    /// the pattern of the declaration binds.
    fn refer(&mut self, r: &Ref, binding: &Binding) -> Result<String, SortError> {
        let index = match &r.index {
            None => None,
            Some(p) => match p.ground(binding) {
                Some(g) => Some(g),
                None => {
                    return error(
                        format!(
                            "the index of {} must be a ground term or a part of the pattern",
                            r.name
                        ),
                        r.position,
                    )
                }
            },
        };
        self.name(&r.name, index.as_ref())
    }

    /// The sort of that name in the form decided by the root symbol.
    /// `within` are the sorts being defined as unions that have this one for
    /// an alternative.
    fn define(&mut self, name: &str, within: &mut Vec<String>) -> Result<SortDef, SortError> {
        if let Some(def) = self.defs.get(name) {
            return Ok(def.clone());
        }
        let instance = match self.known.get(name) {
            Some(instance) => instance.clone(),
            None => return error(format!("unknown sort {}", name), 0),
        };
        if within.iter().any(|n| n == name) {
            return error(
                format!("sort {} is defined as itself", name),
                instance.position,
            );
        }
        let (alts, binding) = match self.choose(&instance.family, instance.index.as_ref()) {
            Some((decl, binding)) => (decl.alts.clone(), binding),
            None => {
                self.defs.insert(name.to_string(), SortDef::empty());
                return Ok(SortDef::empty());
            }
        };
        let undecided = |at: String| SortError {
            message: format!("sort {} is not decided by the root symbol at {}", name, at),
            position: instance.position,
        };
        let mut def = SortDef::empty();
        let mut other = None;
        within.push(name.to_string());
        for alt in &alts {
            let part = match alt {
                Alt::None => continue,
                Alt::Other { arg, excluded } => {
                    let arg = match arg {
                        Some(r) => Some(self.refer(r, &binding)?),
                        None => None,
                    };
                    other = Some((excluded.clone(), arg));
                    continue;
                }
                Alt::Case { sym, children } => {
                    let mut args = Vec::new();
                    for child in children {
                        args.push(match child {
                            Some(r) => Some(self.refer(r, &binding)?),
                            None => None,
                        });
                    }
                    SortDef {
                        cases: vec![(sym.clone(), args)],
                        rest: None,
                    }
                }
                Alt::Ref(r) => {
                    let target = self.refer(r, &binding)?;
                    self.define(&target, within)?
                }
            };
            def = union(&def, &part).map_err(undecided)?;
        }
        within.pop();
        let def = match other {
            Some((excluded, arg)) => with_other(&def, &excluded, &arg),
            None => def,
        };
        self.defs.insert(name.to_string(), def.clone());
        Ok(def)
    }

    /// Declare the named sorts and every sort they refer to, and check that
    /// the sorts are still well formed. On an error nothing is declared.
    fn declare(&mut self, names: Vec<String>) -> Result<(), SortError> {
        let before = self.instances.len();
        let done = self.declare_unchecked(names).and_then(|()| {
            if self.instances.len() == before {
                Ok(())
            } else {
                self.check_well_formed()
            }
        });
        if done.is_err() {
            self.instances.truncate(before);
        }
        done
    }

    fn declare_unchecked(&mut self, names: Vec<String>) -> Result<(), SortError> {
        let mut queue: std::collections::VecDeque<String> = names.into();
        while let Some(name) = queue.pop_front() {
            if self.instances.iter().any(|(n, _)| *n == name) {
                continue;
            }
            let def = self.define(&name, &mut Vec::new())?;
            let args = def.cases.iter().flat_map(|(_, args)| args.iter().flatten());
            let rest = def.rest.iter().flat_map(|(_, arg)| arg.iter());
            queue.extend(args.chain(rest).cloned());
            self.instances.push((name, def));
        }
        Ok(())
    }

    /// The name of the sort a reference denotes: `name` itself, or the
    /// instance of the indexed sort `name` at `index`, declared on demand
    /// with every instance it refers to. An instance that is not decided by
    /// the root symbol, or with which the sorts are not well formed, is an
    /// error, and is not declared.
    pub fn resolve(&mut self, name: &str, index: Option<&Ground>) -> Result<String, SortError> {
        let instance = self.name(name, index)?;
        self.declare(vec![instance.clone()])?;
        Ok(instance)
    }

    /// Every sort declared or needed so far, in the form decided by the root
    /// symbol.
    pub fn table(&self) -> &[(String, SortDef)] {
        &self.instances
    }

    /// Check that the terms common to any of the sorts are none, one, or
    /// infinitely many. The error names sorts with finitely many terms in
    /// common, and more than one.
    pub fn check_well_formed(&self) -> Result<(), SortError> {
        let mut census = Census::new(&self.instances);
        let n = self.instances.len();
        let inside = census.inclusions();
        // Sets of sorts with infinitely many terms in common, none of them
        // inside another. A set with a sort inside another has the terms of
        // the set without the larger sort, and a set with no term or one in
        // common stays so when a sort is added.
        let nested = |x: usize, y: usize| inside[x][y] || inside[y][x];
        let mut open: Vec<Vec<usize>> = vec![Vec::new()];
        while let Some(set) = open.pop() {
            let from = set.last().map_or(0, |last| last + 1);
            for x in from..n {
                if set.iter().any(|&y| nested(x, y)) {
                    continue;
                }
                let mut larger = set.clone();
                larger.push(x);
                match census.count(&larger) {
                    Count::None | Count::One => {}
                    Count::Infinite => open.push(larger),
                    Count::Several => {
                        let names: Vec<&str> = larger
                            .iter()
                            .map(|&i| self.instances[i].0.as_str())
                            .collect();
                        let message = if names.len() == 1 {
                            format!(
                                "the sort {} has finitely many terms, and more than one",
                                names[0]
                            )
                        } else {
                            format!(
                                "the sorts {} have finitely many terms in common, and more than one",
                                names.join(", ")
                            )
                        };
                        let position = self.known.get(names[0]).map_or(0, |i| i.position);
                        return error(message, position);
                    }
                }
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// How many terms sorts have in common
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Count {
    None,
    One,
    /// Finitely many, and more than one.
    Several,
    Infinite,
}

/// What a set of sorts does at the roots that matter.
#[derive(Clone, Debug)]
enum Node {
    /// Every sort of the set has other symbols: the constants no declaration
    /// names are in all of them.
    Open,
    /// For each root all the sorts accept: for each argument, the set of
    /// sorts it must be in, as a node.
    Closed(Vec<Vec<usize>>),
}

struct Census<'a> {
    defs: Vec<&'a SortDef>,
    ids: BTreeMap<&'a str, usize>,
    sets: BTreeMap<Vec<usize>, usize>,
    nodes: Vec<Option<Node>>,
    members: Vec<Vec<usize>>,
}

impl<'a> Census<'a> {
    fn new(table: &'a [(String, SortDef)]) -> Census<'a> {
        let mut ids = BTreeMap::new();
        let mut defs = Vec::new();
        for (name, def) in table {
            if !ids.contains_key(name.as_str()) {
                ids.insert(name.as_str(), defs.len());
                defs.push(def);
            }
        }
        Census {
            defs,
            ids,
            sets: BTreeMap::new(),
            nodes: Vec::new(),
            members: Vec::new(),
        }
    }

    /// `inside[x][y]`: every term of sort `x` is shown to be in sort `y`.
    /// Where it is false the sort may still be inside.
    fn inclusions(&self) -> Vec<Vec<bool>> {
        let n = self.defs.len();
        let mut inside = vec![vec![true; n]; n];
        // A sort named with no declaration has no term: the argument is
        // then in every sort, and no declared sort is shown inside it.
        let arg_inside =
            |inside: &Vec<Vec<bool>>, x: &Option<String>, y: &Option<String>| match (x, y) {
                (_, None) => true,
                (None, Some(_)) => false,
                (Some(a), Some(b)) => match (self.ids.get(a.as_str()), self.ids.get(b.as_str())) {
                    (None, _) => true,
                    (Some(_), None) => false,
                    (Some(&i), Some(&j)) => inside[i][j],
                },
            };
        loop {
            let mut changed = false;
            for x in 0..n {
                for y in 0..n {
                    if !inside[x][y] {
                        continue;
                    }
                    let (a, b) = (self.defs[x], self.defs[y]);
                    let mut keys = Vec::new();
                    a.keys(&mut keys);
                    b.keys(&mut keys);
                    let at_keys = keys.iter().all(|(f, m)| match a.step(f, *m) {
                        None => true,
                        Some(xs) => match b.step(f, *m) {
                            None => false,
                            Some(ys) => xs.iter().zip(&ys).all(|(p, q)| arg_inside(&inside, p, q)),
                        },
                    });
                    let at_others = match (&a.rest, &b.rest) {
                        (None, _) => true,
                        (Some(_), None) => false,
                        (Some((_, p)), Some((_, q))) => arg_inside(&inside, p, q),
                    };
                    if !(at_keys && at_others) {
                        inside[x][y] = false;
                        changed = true;
                    }
                }
            }
            if !changed {
                return inside;
            }
        }
    }

    fn node(&mut self, mut set: Vec<usize>) -> usize {
        set.sort_unstable();
        set.dedup();
        if let Some(&id) = self.sets.get(&set) {
            return id;
        }
        let id = self.nodes.len();
        self.sets.insert(set.clone(), id);
        self.nodes.push(None);
        self.members.push(set);
        id
    }

    /// The set of sorts an argument must be in. `None` when one of them has
    /// no declaration: no term is in it.
    fn argument(&self, sorts: &[&Option<String>]) -> Option<Vec<usize>> {
        let mut set = Vec::new();
        for name in sorts.iter().copied().flatten() {
            set.push(*self.ids.get(name.as_str())?);
        }
        Some(set)
    }

    fn expand(&mut self, id: usize) {
        if self.nodes[id].is_some() {
            return;
        }
        let set = self.members[id].clone();
        let closed = set.iter().find(|&&s| self.defs[s].rest.is_none());
        let node = match closed {
            None => Node::Open,
            Some(&s) => {
                let mut keys = Vec::new();
                self.defs[s].keys(&mut keys);
                let mut roots = Vec::new();
                for (f, n) in &keys {
                    let steps: Option<Vec<Vec<Option<String>>>> =
                        set.iter().map(|&m| self.defs[m].step(f, *n)).collect();
                    let Some(steps) = steps else { continue };
                    let args: Option<Vec<Vec<usize>>> = (0..*n)
                        .map(|i| {
                            let at: Vec<&Option<String>> = steps.iter().map(|s| &s[i]).collect();
                            self.argument(&at)
                        })
                        .collect();
                    let Some(args) = args else { continue };
                    roots.push(args.into_iter().map(|a| self.node(a)).collect());
                }
                Node::Closed(roots)
            }
        };
        self.nodes[id] = Some(node);
    }

    /// How many terms the sorts of the set have in common.
    fn count(&mut self, set: &[usize]) -> Count {
        let root = self.node(set.to_vec());
        // Every set of sorts an argument below may have to be in.
        let mut reach = vec![root];
        let mut seen = BTreeSet::from([root]);
        let mut next = 0;
        while next < reach.len() {
            let id = reach[next];
            next += 1;
            self.expand(id);
            if let Some(Node::Closed(roots)) = &self.nodes[id] {
                for &child in roots.iter().flatten() {
                    if seen.insert(child) {
                        reach.push(child);
                    }
                }
            }
        }
        let roots_of = |id: usize| -> Option<&Vec<Vec<usize>>> {
            match &self.nodes[id] {
                Some(Node::Closed(roots)) => Some(roots),
                _ => None,
            }
        };
        // Sets with a term in common: the least such that are open, or have
        // a root whose arguments all have a term.
        let mut live: BTreeSet<usize> = BTreeSet::new();
        loop {
            let before = live.len();
            for &id in &reach {
                let has = match roots_of(id) {
                    None => true,
                    Some(roots) => roots
                        .iter()
                        .any(|args| args.iter().all(|a| live.contains(a))),
                };
                if has {
                    live.insert(id);
                }
            }
            if live.len() == before {
                break;
            }
        }
        if !live.contains(&root) {
            return Count::None;
        }
        // Sets with finitely many terms in common: the least such that are
        // not open and, at every root with a term, have finitely many terms
        // at each argument.
        let mut finite: BTreeSet<usize> = BTreeSet::new();
        loop {
            let before = finite.len();
            for &id in &reach {
                let Some(roots) = roots_of(id) else { continue };
                let all = roots
                    .iter()
                    .filter(|args| args.iter().all(|a| live.contains(a)))
                    .all(|args| args.iter().all(|a| finite.contains(a)));
                if all {
                    finite.insert(id);
                }
            }
            if finite.len() == before {
                break;
            }
        }
        if !finite.contains(&root) {
            return Count::Infinite;
        }
        // Among those, the number of terms up to two: the sum over the roots
        // of the product over the arguments.
        let mut number: BTreeMap<usize, u8> = BTreeMap::new();
        loop {
            let mut changed = false;
            for &id in &reach {
                if !finite.contains(&id) {
                    continue;
                }
                let Some(roots) = roots_of(id) else { continue };
                let mut sum: u8 = 0;
                for args in roots {
                    let mut product: u8 = 1;
                    for a in args {
                        product = (product * number.get(a).copied().unwrap_or(0)).min(2);
                    }
                    sum = (sum + product).min(2);
                }
                if number.get(&id).copied().unwrap_or(0) != sum {
                    number.insert(id, sum);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        match number.get(&root).copied().unwrap_or(0) {
            0 => Count::None,
            1 => Count::One,
            _ => Count::Several,
        }
    }
}

/// Does the ground term belong to the sort of that name? A name with no
/// declaration is the empty sort.
pub fn member(table: &[(String, SortDef)], name: &str, t: &Ground) -> bool {
    let Some((_, def)) = table.iter().find(|(n, _)| n == name) else {
        return false;
    };
    match def.step(&t.sym, t.args.len()) {
        None => false,
        Some(sorts) => sorts.iter().zip(&t.args).all(|(sort, arg)| match sort {
            None => true,
            Some(s) => member(table, s, arg),
        }),
    }
}

/// Read a ground term: `c` or `(f t1 ... tn)`.
pub fn parse_ground(src: &str) -> Result<Ground, SortError> {
    let mut reader = Reader::new(src)?;
    if let Some((_, position)) = reader.toks.iter().find(|(t, _)| matches!(t, Tok::Var(_))) {
        return error("a ground term has no variable", *position);
    }
    let pattern = reader.pattern("a term")?;
    if *reader.peek() != Tok::End {
        return reader.fail("the end of the term");
    }
    match pattern.ground(&Binding::new()) {
        Some(g) => Ok(g),
        None => error("a ground term has no variable", 0),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const N: &str = "sort n = z | (s n)\n";
    const M: &str = "sort m = z | (t m)\n";
    const D: &str = "sort d(z) = none\nsort d((s $n)) = (neg d($n)) | (k _)\n";

    fn env(src: &str) -> SortEnv {
        match SortEnv::parse(src) {
            Ok(e) => e,
            Err(e) => panic!("rejected: {}\n{}", e, src),
        }
    }

    fn rejected(src: &str, why: &str) -> SortError {
        match SortEnv::parse(src) {
            Ok(e) => panic!("accepted, with {:?}\n{}", e.table(), src),
            Err(e) => {
                assert!(
                    e.message.contains(why),
                    "rejected with `{}`, expected `{}`\n{}",
                    e.message,
                    why,
                    src
                );
                e
            }
        }
    }

    fn g(src: &str) -> Ground {
        match parse_ground(src) {
            Ok(t) => t,
            Err(e) => panic!("not a ground term: {}\n{}", e, src),
        }
    }

    fn has(env: &SortEnv, name: &str, t: &str) -> bool {
        member(env.table(), name, &g(t))
    }

    fn def<'a>(env: &'a SortEnv, name: &str) -> &'a SortDef {
        match env.table().iter().find(|(n, _)| n == name) {
            Some((_, d)) => d,
            None => panic!("no sort {} in {:?}", name, env.table()),
        }
    }

    fn some(s: &str) -> Option<String> {
        Some(s.to_string())
    }

    fn case(f: &str, args: Vec<Option<String>>) -> (String, Vec<Option<String>>) {
        (f.to_string(), args)
    }

    fn key(f: &str, n: usize) -> (String, usize) {
        (f.to_string(), n)
    }

    // ---- ground terms ----

    #[test]
    fn ground_constant() {
        assert_eq!(parse_ground("c"), Ok(Ground::atom("c")));
    }

    #[test]
    fn ground_nested() {
        let want = Ground::new(
            "f",
            vec![Ground::atom("a"), Ground::new("g", vec![Ground::atom("b")])],
        );
        assert_eq!(parse_ground("(f a (g b))"), Ok(want));
    }

    #[test]
    fn ground_spaces_ignored() {
        assert_eq!(
            parse_ground("  ( f  a ) "),
            Ok(Ground::new("f", vec![Ground::atom("a")]))
        );
    }

    #[test]
    fn ground_parenthesised_constant_is_the_constant() {
        assert_eq!(parse_ground("(f)"), Ok(Ground::atom("f")));
    }

    #[test]
    fn ground_displays_as_it_is_read() {
        assert_eq!(g("(f a (g b))").to_string(), "(f a (g b))");
    }

    #[test]
    fn ground_empty_text_rejected() {
        let e = parse_ground("").unwrap_err();
        assert!(e.message.contains("expected a term"), "{}", e);
    }

    #[test]
    fn ground_unclosed_rejected() {
        let e = parse_ground("(f a").unwrap_err();
        assert!(e.message.contains("expected `)`"), "{}", e);
    }

    #[test]
    fn ground_two_terms_rejected() {
        let e = parse_ground("a b").unwrap_err();
        assert!(e.message.contains("expected the end"), "{}", e);
        assert_eq!(e.position, 2);
    }

    #[test]
    fn ground_stray_close_rejected() {
        let e = parse_ground(")").unwrap_err();
        assert!(e.message.contains("expected a term"), "{}", e);
    }

    #[test]
    fn ground_empty_parens_rejected() {
        let e = parse_ground("()").unwrap_err();
        assert!(e.message.contains("expected a symbol"), "{}", e);
    }

    #[test]
    fn ground_variable_rejected() {
        let e = parse_ground("(f $x)").unwrap_err();
        assert!(e.message.contains("no variable"), "{}", e);
        assert_eq!(e.position, 3);
    }

    #[test]
    fn ground_unknown_character_rejected() {
        let e = parse_ground("a,b").unwrap_err();
        assert!(e.message.contains("unexpected character"), "{}", e);
        assert_eq!(e.position, 1);
    }

    // ---- membership on tables written by hand ----

    #[test]
    fn member_undeclared_name_is_empty() {
        assert!(!member(&[], "a", &g("x")));
    }

    #[test]
    fn member_argument_in_undeclared_sort_is_false() {
        let table = vec![(
            "a".to_string(),
            SortDef {
                cases: vec![case("f", vec![some("zz")])],
                rest: None,
            },
        )];
        assert!(!member(&table, "a", &g("(f x)")));
    }

    #[test]
    fn member_case_is_read_before_the_rest() {
        let table = vec![
            (
                "a".to_string(),
                SortDef {
                    cases: vec![case("f", vec![some("e")])],
                    rest: Some((vec![], None)),
                },
            ),
            (
                "e".to_string(),
                SortDef {
                    cases: vec![],
                    rest: None,
                },
            ),
        ];
        assert!(!member(&table, "a", &g("(f x)")));
        assert!(member(&table, "a", &g("(g x)")));
    }

    #[test]
    fn member_first_case_for_a_root_is_the_one_read() {
        let table = vec![(
            "a".to_string(),
            SortDef {
                cases: vec![case("f", vec![some("e")]), case("f", vec![None])],
                rest: None,
            },
        )];
        assert!(!member(&table, "a", &g("(f x)")));
    }

    #[test]
    fn member_exclusion_counts_arguments() {
        let table = vec![(
            "a".to_string(),
            SortDef {
                cases: vec![],
                rest: Some((vec![key("f", 1)], None)),
            },
        )];
        assert!(!member(&table, "a", &g("(f a)")));
        assert!(member(&table, "a", &g("f")));
        assert!(member(&table, "a", &g("(f a b)")));
    }

    #[test]
    fn member_rest_sends_every_argument_to_its_sort() {
        let table = vec![(
            "a".to_string(),
            SortDef {
                cases: vec![case("c", vec![])],
                rest: Some((vec![], some("a"))),
            },
        )];
        assert!(member(&table, "a", &g("(f c (g c))")));
        assert!(member(&table, "a", &g("(f c (g c) q)")));
    }

    // ---- reading declarations ----

    #[test]
    fn parse_empty_text_declares_nothing() {
        assert!(env("").table().is_empty());
        assert!(env("  # nothing\n").table().is_empty());
    }

    #[test]
    fn parse_constant() {
        let e = env("sort a = b");
        assert_eq!(
            e.table(),
            &[(
                "a".to_string(),
                SortDef {
                    cases: vec![case("b", vec![])],
                    rest: None
                }
            )]
        );
        assert!(has(&e, "a", "b"));
        assert!(!has(&e, "a", "c"));
        assert!(!has(&e, "a", "(b b)"));
    }

    #[test]
    fn parse_none_is_the_empty_sort() {
        let e = env("sort e = none");
        assert_eq!(
            def(&e, "e"),
            &SortDef {
                cases: vec![],
                rest: None
            }
        );
        assert!(!has(&e, "e", "none"));
    }

    #[test]
    fn parse_case_with_any_argument() {
        let e = env("sort pos = (s _)");
        assert_eq!(
            def(&e, "pos"),
            &SortDef {
                cases: vec![case("s", vec![None])],
                rest: None
            }
        );
        assert!(has(&e, "pos", "(s z)"));
        assert!(has(&e, "pos", "(s (q q))"));
        assert!(!has(&e, "pos", "s"));
        assert!(!has(&e, "pos", "(s z z)"));
    }

    #[test]
    fn parse_recursive_sort() {
        let e = env(N);
        assert_eq!(
            def(&e, "n"),
            &SortDef {
                cases: vec![case("z", vec![]), case("s", vec![some("n")])],
                rest: None
            }
        );
        assert!(has(&e, "n", "z"));
        assert!(has(&e, "n", "(s (s z))"));
        assert!(!has(&e, "n", "(s q)"));
        assert!(!has(&e, "n", "(t z)"));
    }

    #[test]
    fn parse_other_is_every_term() {
        let e = env("sort any = other");
        assert_eq!(
            def(&e, "any"),
            &SortDef {
                cases: vec![],
                rest: Some((vec![], None))
            }
        );
        assert!(has(&e, "any", "a"));
        assert!(has(&e, "any", "(f a b)"));
    }

    #[test]
    fn parse_other_with_exclusions() {
        let e = env("sort name = other \\ (app _ _) \\ (lam _ _)");
        assert_eq!(
            def(&e, "name"),
            &SortDef {
                cases: vec![],
                rest: Some((vec![key("app", 2), key("lam", 2)], None))
            }
        );
        assert!(!has(&e, "name", "(app a b)"));
        assert!(has(&e, "name", "(app a)"));
        assert!(has(&e, "name", "app"));
        assert!(has(&e, "name", "x"));
    }

    #[test]
    fn parse_other_excluding_a_constant() {
        let e = env("sort x = other \\ a");
        assert_eq!(def(&e, "x").rest, Some((vec![key("a", 0)], None)));
        assert!(!has(&e, "x", "a"));
        assert!(has(&e, "x", "(a b)"));
        assert!(has(&e, "x", "b"));
    }

    #[test]
    fn parse_exclusion_of_parenthesised_constant() {
        let e = env("sort x = other \\ (a)");
        assert_eq!(def(&e, "x").rest, Some((vec![key("a", 0)], None)));
    }

    #[test]
    fn parse_other_of_sends_arguments_to_the_sort() {
        let e = env("sort noc = other of noc \\ (c _)");
        assert_eq!(
            def(&e, "noc"),
            &SortDef {
                cases: vec![],
                rest: Some((vec![key("c", 1)], some("noc")))
            }
        );
        assert!(has(&e, "noc", "(f a (g b))"));
        assert!(has(&e, "noc", "c"));
        assert!(!has(&e, "noc", "(c a)"));
        assert!(!has(&e, "noc", "(f (c a))"));
    }

    #[test]
    fn parse_other_of_the_empty_sort_is_the_constants() {
        let e = env("sort e = none\nsort leaf = other of e");
        assert!(has(&e, "leaf", "a"));
        assert!(!has(&e, "leaf", "(f a)"));
    }

    #[test]
    fn parse_other_leaves_the_cases_as_written() {
        let e = env("sort n = z | (s n)\nsort w = (neg n) | other");
        assert_eq!(
            def(&e, "w"),
            &SortDef {
                cases: vec![case("neg", vec![some("n")])],
                rest: Some((vec![], None))
            }
        );
        assert!(has(&e, "w", "(neg z)"));
        assert!(!has(&e, "w", "(neg q)"));
        assert!(has(&e, "w", "(g q)"));
        assert!(has(&e, "w", "(neg q q)"));
    }

    #[test]
    fn parse_other_written_first_still_leaves_the_cases() {
        let e = env("sort n = z | (s n)\nsort w = other | (neg n)");
        assert!(!has(&e, "w", "(neg q)"));
        assert!(has(&e, "w", "(g q)"));
    }

    #[test]
    fn parse_other_exclusion_of_a_written_case_keeps_the_case() {
        let e = env("sort n = z | (s n)\nsort u = (f n) | other \\ (f _) \\ (h _)");
        assert_eq!(
            def(&e, "u"),
            &SortDef {
                cases: vec![case("f", vec![some("n")])],
                rest: Some((vec![key("h", 1)], None))
            }
        );
        assert!(has(&e, "u", "(f z)"));
        assert!(!has(&e, "u", "(f q)"));
        assert!(!has(&e, "u", "(h q)"));
        assert!(has(&e, "u", "g"));
    }

    #[test]
    fn parse_other_fills_what_a_referenced_sort_rejects() {
        // `name` rejects app/2 and lam/2; `other of e` gives those roots with
        // arguments in `e`, and leaves the roots `name` accepts alone.
        let e = env("sort e = none\n\
             sort name = other \\ (app _ _) \\ (lam _ _)\n\
             sort w = name | other of e \\ (lam _ _)");
        assert!(has(&e, "w", "(f (f a))"));
        assert!(!has(&e, "w", "(lam a b)"));
        assert!(!has(&e, "w", "(app a b)"));
        assert_eq!(
            def(&e, "w"),
            &SortDef {
                cases: vec![case("app", vec![some("e"), some("e")])],
                rest: Some((vec![key("lam", 2)], None))
            }
        );
    }

    #[test]
    fn parse_other_twice_rejected() {
        rejected("sort a = other | other \\ c", "`other` twice");
    }

    #[test]
    fn parse_comments_and_spacing() {
        let e = env("# head\n\n  sort   n=z|(s n)   # tail\n");
        assert_eq!(e.table(), env(N).table());
    }

    #[test]
    fn parse_alternatives_on_several_lines() {
        let e = env("sort n = z\n  | (s n)");
        assert_eq!(e.table(), env(N).table());
    }

    #[test]
    fn parse_reference_to_a_sort_declared_later() {
        let e = env("sort a = b\nsort b = c");
        assert!(has(&e, "a", "c"));
        assert!(!has(&e, "a", "b"));
    }

    #[test]
    fn parse_table_lists_sorts_in_the_order_declared() {
        let e = env("sort b = (f a)\nsort a = z");
        let names: Vec<&str> = e.table().iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, vec!["b", "a"]);
    }

    #[test]
    fn parse_examples_of_the_design_note() {
        let e = env("sort prog = l | (b prog) | (f prog prog)\n\
             sort sk   = k | s | (a sk sk)\n\
             sort name = other \\ (app _ _) \\ (lam _ _)\n\
             sort neut = name | (app neut norm)\n\
             sort norm = neut | (lam _ norm)\n\
             sort pos  = (s _)\n");
        assert_eq!(
            def(&e, "neut"),
            &SortDef {
                cases: vec![case("app", vec![some("neut"), some("norm")])],
                rest: Some((vec![key("lam", 2)], None))
            }
        );
        assert_eq!(
            def(&e, "norm"),
            &SortDef {
                cases: vec![
                    case("app", vec![some("neut"), some("norm")]),
                    case("lam", vec![None, some("norm")])
                ],
                rest: Some((vec![], None))
            }
        );
        assert!(has(&e, "neut", "(app x (lam y x))"));
        assert!(has(&e, "norm", "(lam y x)"));
        assert!(!has(&e, "neut", "(lam y x)"));
        assert!(!has(&e, "norm", "(app (lam y y) x)"));
    }

    // ---- constants and names of sorts ----

    #[test]
    fn parenthesised_name_of_a_sort_is_the_constant() {
        let e = env("sort n = z | (s n)\nsort w = (n) | (s n)");
        assert!(has(&e, "w", "n"));
        assert!(has(&e, "w", "(s z)"));
        assert!(!has(&e, "w", "z"));
    }

    #[test]
    fn bare_name_of_a_sort_is_the_sort() {
        let e = env("sort n = z | (s n)\nsort w = n");
        assert!(has(&e, "w", "z"));
        assert!(!has(&e, "w", "n"));
    }

    #[test]
    fn sort_with_the_constant_of_its_own_name() {
        let e = env("sort z = (z)");
        assert!(has(&e, "z", "z"));
    }

    #[test]
    fn reserved_word_as_parenthesised_constant() {
        let e = env("sort a = (none) | (f a)");
        assert!(has(&e, "a", "(f none)"));
    }

    #[test]
    fn reserved_word_is_not_the_name_of_a_sort() {
        rejected("sort other = a", "expected the name of a sort");
    }

    // ---- unions ----

    #[test]
    fn union_of_equal_cases_is_one_case() {
        let e = env("sort n = z | (s n)\nsort u = (f n) | (f n)");
        assert_eq!(def(&e, "u").cases, vec![case("f", vec![some("n")])]);
    }

    #[test]
    fn union_takes_the_case_that_accepts_more() {
        let e = env("sort n = z | (s n)\nsort u = (f n _) | (f _ _)");
        assert_eq!(def(&e, "u").cases, vec![case("f", vec![None, None])]);
        let e = env("sort n = z | (s n)\nsort u = (f _ _) | (f n _)");
        assert_eq!(def(&e, "u").cases, vec![case("f", vec![None, None])]);
    }

    #[test]
    fn union_of_one_constant_twice() {
        let e = env("sort n = z | (s n)\nsort u = z | z | (s n)");
        assert_eq!(def(&e, "u"), def(&e, "n"));
    }

    #[test]
    fn union_keeps_one_symbol_with_different_numbers_of_arguments() {
        let e = env("sort n = z | (s n)\nsort u = (f n) | (f n n) | f");
        assert_eq!(
            def(&e, "u").cases,
            vec![
                case("f", vec![some("n")]),
                case("f", vec![some("n"), some("n")]),
                case("f", vec![])
            ]
        );
    }

    #[test]
    fn union_of_incomparable_cases_rejected() {
        let e = rejected(
            "sort n = z | (s n)\nsort u = (f n _) | (f _ n)",
            "sort u is not decided by the root symbol at f/2",
        );
        assert_eq!(e.position, 19);
    }

    #[test]
    fn union_of_cases_in_different_sorts_rejected() {
        let src = format!("{}{}sort u = (f n) | (f m)", N, M);
        rejected(&src, "not decided by the root symbol at f/1");
    }

    #[test]
    fn union_with_a_named_sort_merges() {
        let e = env("sort n = z | (s n)\nsort ab = (f n)\nsort c = ab | (f _)");
        assert_eq!(def(&e, "c").cases, vec![case("f", vec![None])]);
    }

    #[test]
    fn union_with_a_named_sort_rejected_when_not_decided() {
        let src = format!("{}{}sort ab = (f n)\nsort c = ab | (f m)", N, M);
        rejected(&src, "sort c is not decided by the root symbol at f/1");
    }

    #[test]
    fn union_of_two_sorts_with_other_symbols() {
        // `a` has the other symbols with arguments in `a`, `b` with any
        // arguments; `b` leaves out g/1, which `a` has.
        let e = env("sort a = other of a \\ (c _)\n\
             sort b = other \\ (g _) \\ (c _)\n\
             sort u = a | b");
        assert_eq!(
            def(&e, "u"),
            &SortDef {
                cases: vec![case("g", vec![some("a")])],
                rest: Some((vec![key("c", 1)], None))
            }
        );
        assert!(has(&e, "u", "(f (c x))"));
        assert!(!has(&e, "u", "(g (c x))"));
        assert!(has(&e, "u", "(g (f x))"));
        assert!(!has(&e, "u", "(c x)"));
    }

    #[test]
    fn union_of_sorts_whose_other_symbols_disagree_rejected() {
        let src = format!(
            "{}{}sort a = other of n\nsort b = other of m\nsort u = a | b",
            N, M
        );
        rejected(
            &src,
            "sort u is not decided by the root symbol at the other symbols",
        );
    }

    #[test]
    fn union_naming_one_sort_twice_down_a_long_chain_is_read_quickly() {
        // Each sort is worked out once, not once for each way down to it.
        let mut src = String::new();
        for i in 0..60 {
            src.push_str(&format!("sort c{} = c{} | c{}\n", i, i + 1, i + 1));
        }
        src.push_str("sort c60 = (k _)\n");
        let e = env(&src);
        assert_eq!(def(&e, "c0"), def(&e, "c60"));
    }

    #[test]
    fn sort_that_is_itself_rejected() {
        rejected("sort z = z", "sort z is defined as itself");
        rejected("sort a = a | b", "sort a is defined as itself");
    }

    #[test]
    fn sort_that_is_itself_through_another_rejected() {
        rejected("sort a = b | x\nsort b = a | (f b)", "is defined as itself");
    }

    #[test]
    fn sort_under_its_own_constructor_is_accepted() {
        let e = env("sort a = (f a)");
        assert!(!has(&e, "a", "(f (f a))"));
    }

    // ---- unknown and repeated sorts ----

    #[test]
    fn unknown_sort_of_an_argument_rejected() {
        let e = rejected("sort a = (f b)", "unknown sort b");
        assert_eq!(e.position, 12);
    }

    #[test]
    fn unknown_sort_after_other_of_rejected() {
        rejected("sort a = other of b", "unknown sort b");
    }

    #[test]
    fn unknown_sort_with_an_index_rejected() {
        rejected("sort a = b(z)", "unknown sort b");
    }

    #[test]
    fn sort_declared_twice_rejected() {
        let e = rejected("sort a = x\nsort a = y", "sort a is declared twice");
        assert_eq!(e.position, 11);
    }

    #[test]
    fn sort_declared_with_and_without_index_rejected() {
        rejected(
            "sort d = a\nsort d(z) = none",
            "sort d is declared with and without an index",
        );
    }

    // ---- indexed sorts ----

    #[test]
    fn resolve_plain_sort_is_its_name() {
        let mut e = env(N);
        assert_eq!(e.resolve("n", None), Ok("n".to_string()));
        assert_eq!(e.table().len(), 1);
    }

    #[test]
    fn indexed_declarations_alone_declare_no_sort() {
        assert!(env(D).table().is_empty());
    }

    #[test]
    fn resolve_instance_is_named_by_its_index() {
        let mut e = env(D);
        assert_eq!(
            e.resolve("d", Some(&g("(s z)"))),
            Ok("d((s z))".to_string())
        );
        assert!(has(&e, "d((s z))", "(k a)"));
        assert!(!has(&e, "d((s z))", "(neg (k a))"));
    }

    #[test]
    fn resolve_declares_the_instances_it_refers_to() {
        let mut e = env(D);
        let name = e.resolve("d", Some(&g("(s (s z))"))).unwrap();
        assert!(has(&e, &name, "(neg (k a))"));
        assert!(!has(&e, &name, "(neg (neg (k a)))"));
        let names: Vec<&str> = e.table().iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, vec!["d((s (s z)))", "d((s z))", "d(z)"]);
        assert_eq!(
            def(&e, "d((s (s z)))"),
            &SortDef {
                cases: vec![case("neg", vec![some("d((s z))")]), case("k", vec![None])],
                rest: None
            }
        );
    }

    #[test]
    fn resolve_index_no_declaration_matches_is_the_empty_sort() {
        let mut e = env(D);
        let name = e.resolve("d", Some(&g("q"))).unwrap();
        assert_eq!(
            def(&e, &name),
            &SortDef {
                cases: vec![],
                rest: None
            }
        );
    }

    #[test]
    fn resolve_twice_declares_once() {
        let mut e = env(D);
        let a = e.resolve("d", Some(&g("(s z)"))).unwrap();
        let len = e.table().len();
        let b = e.resolve("d", Some(&g("(s z)"))).unwrap();
        assert_eq!(a, b);
        assert_eq!(e.table().len(), len);
    }

    #[test]
    fn resolve_unknown_sort_rejected() {
        let mut e = env(N);
        let err = e.resolve("nope", None).unwrap_err();
        assert!(err.message.contains("unknown sort nope"), "{}", err);
    }

    #[test]
    fn resolve_plain_sort_with_index_rejected() {
        let mut e = env(N);
        let err = e.resolve("n", Some(&g("z"))).unwrap_err();
        assert!(err.message.contains("sort n has no index"), "{}", err);
    }

    #[test]
    fn resolve_indexed_sort_without_index_rejected() {
        let mut e = env(D);
        let err = e.resolve("d", None).unwrap_err();
        assert!(err.message.contains("sort d needs an index"), "{}", err);
    }

    #[test]
    fn resolve_pattern_with_a_repeated_variable_needs_equal_parts() {
        let mut e = env("sort e((p $x $x)) = (same _)\n");
        let eq = e.resolve("e", Some(&g("(p a a)"))).unwrap();
        let ne = e.resolve("e", Some(&g("(p a b)"))).unwrap();
        assert!(has(&e, &eq, "(same q)"));
        assert!(!has(&e, &ne, "(same q)"));
    }

    #[test]
    fn resolve_instance_that_is_itself_rejected_and_not_declared() {
        let mut e = env("sort d($n) = d($n) | (k _)\n");
        let err = e.resolve("d", Some(&g("z"))).unwrap_err();
        assert!(
            err.message.contains("sort d(z) is defined as itself"),
            "{}",
            err
        );
        assert!(e.table().is_empty());
    }

    #[test]
    fn resolve_instance_not_decided_by_the_root_rejected() {
        let mut e = env("sort n = z | (s n)\nsort d(a) = (k _)\nsort d(b) = (j _)\n\
             sort w($i) = (f d($i)) | (f d(a))\n");
        assert!(e.resolve("w", Some(&g("a"))).is_ok());
        let err = e.resolve("w", Some(&g("b"))).unwrap_err();
        assert!(
            err.message
                .contains("sort w(b) is not decided by the root symbol at f/1"),
            "{}",
            err
        );
    }

    #[test]
    fn declarations_with_the_same_pattern_rejected() {
        rejected(
            "sort d(z) = none\nsort d(z) = none",
            "the declarations of sort d overlap",
        );
    }

    #[test]
    fn declarations_overlapping_at_a_variable_rejected() {
        rejected(
            "sort d($n) = none\nsort d(z) = (k _)",
            "the declarations of sort d overlap",
        );
    }

    #[test]
    fn declarations_overlapping_below_the_root_rejected() {
        rejected(
            "sort d((s $n)) = none\nsort d((s z)) = (k _)",
            "the declarations of sort d overlap",
        );
    }

    #[test]
    fn declarations_overlapping_only_through_two_variables_rejected() {
        rejected(
            "sort d((p $x a)) = none\nsort d((p b $y)) = none",
            "the declarations of sort d overlap",
        );
    }

    #[test]
    fn declarations_with_repeated_variable_that_cannot_meet_accepted() {
        // (p $x $x) and (p a b) have no common instance.
        env("sort d((p $x $x)) = none\nsort d((p a b)) = none");
    }

    #[test]
    fn declarations_with_variable_inside_itself_do_not_overlap() {
        // (p $x $x) and (p $y (s $y)) have no common instance.
        env("sort d((p $x $x)) = none\nsort d((p $y (s $y))) = none");
    }

    #[test]
    fn reference_indexed_by_a_ground_term() {
        let mut e = env("sort d(z) = (k _)\nsort d((s $n)) = (f d(z))");
        let name = e.resolve("d", Some(&g("(s q)"))).unwrap();
        assert!(has(&e, &name, "(f (k a))"));
    }

    #[test]
    fn reference_indexed_by_parts_of_the_pattern() {
        let mut e = env("sort d(z) = (k _)\nsort d((p (s $n) $m)) = (f d((s $n)) d($m))");
        let name = e.resolve("d", Some(&g("(p (s a) z)"))).unwrap();
        assert_eq!(
            def(&e, &name).cases,
            vec![case("f", vec![some("d((s a))"), some("d(z)")])]
        );
    }

    #[test]
    fn reference_indexed_by_the_whole_pattern() {
        let mut e = env("sort d((s $n)) = (f d((s $n))) | (k _)");
        let name = e.resolve("d", Some(&g("(s z)"))).unwrap();
        assert!(has(&e, &name, "(f (f (k a)))"));
        assert_eq!(e.table().len(), 1);
    }

    #[test]
    fn reference_indexed_by_a_larger_term_rejected() {
        rejected(
            "sort d($n) = (f d((s $n)))",
            "the index of d must be a ground term or a part of the pattern",
        );
    }

    #[test]
    fn reference_indexed_by_an_unknown_variable_rejected() {
        rejected(
            "sort d((s $n)) = (f d($m))",
            "the index of d must be a ground term or a part of the pattern",
        );
    }

    #[test]
    fn reference_with_variable_in_a_plain_declaration_rejected() {
        let src = format!("{}sort w = (f d($n))", D);
        rejected(&src, "the index of d must be a ground term");
    }

    #[test]
    fn reference_with_ground_index_in_a_plain_declaration() {
        let src = format!("{}sort w = (f d((s z)))", D);
        let e = env(&src);
        assert!(has(&e, "w", "(f (k a))"));
        let names: Vec<&str> = e.table().iter().map(|(n, _)| n.as_str()).collect();
        assert_eq!(names, vec!["w", "d((s z))", "d(z)"]);
    }

    #[test]
    fn reference_to_plain_sort_with_index_rejected() {
        rejected(
            "sort n = z | (s n)\nsort w = (f n(z))",
            "sort n has no index",
        );
    }

    #[test]
    fn reference_to_indexed_sort_without_index_rejected() {
        let src = format!("{}sort w = (f d)", D);
        rejected(&src, "sort d needs an index");
    }

    #[test]
    fn indexed_sort_as_an_alternative() {
        let src = format!("{}sort w = d((s z)) | (g w)", D);
        let e = env(&src);
        assert!(has(&e, "w", "(g (k a))"));
    }

    #[test]
    fn index_must_touch_the_name() {
        // With a space, `(g)` is not an index, and an argument is a sort or `_`.
        rejected(
            "sort n = z | (s n)\nsort a = (f n (g))",
            "expected a sort or `_`",
        );
        rejected("sort d (z) = none", "expected `=`");
    }

    // ---- text that is not a declaration ----

    #[test]
    fn missing_equals_rejected() {
        let e = rejected("sort a b", "expected `=`");
        assert_eq!(e.position, 7);
    }

    #[test]
    fn end_after_the_name_rejected() {
        let e = rejected("sort a", "expected `=`");
        assert_eq!(e.position, 6);
    }

    #[test]
    fn end_after_equals_rejected() {
        rejected("sort a =", "expected an alternative");
    }

    #[test]
    fn missing_name_rejected() {
        rejected("sort = a", "expected the name of a sort");
    }

    #[test]
    fn missing_sort_keyword_rejected() {
        let e = rejected("a = b", "expected `sort`");
        assert_eq!(e.position, 0);
    }

    #[test]
    fn unclosed_case_rejected() {
        rejected("sort a = (f _", "expected a sort or `_`");
    }

    #[test]
    fn stray_close_paren_rejected() {
        let e = rejected("sort a = b )", "expected `sort`");
        assert_eq!(e.position, 11);
    }

    #[test]
    fn empty_parens_rejected() {
        rejected("sort a = ()", "expected a symbol");
    }

    #[test]
    fn leading_bar_rejected() {
        rejected("sort a = | b", "expected an alternative");
    }

    #[test]
    fn trailing_bar_rejected() {
        rejected("sort a = b |", "expected an alternative");
    }

    #[test]
    fn empty_alternative_rejected() {
        rejected("sort a = b | | c", "expected an alternative");
    }

    #[test]
    fn case_inside_a_case_rejected() {
        rejected("sort a = (f (g _))", "expected a sort or `_`");
    }

    #[test]
    fn exclusion_without_other_rejected() {
        rejected("sort a = b \\ c", "an exclusion follows `other`");
    }

    #[test]
    fn exclusion_with_a_sort_for_an_argument_rejected() {
        rejected(
            "sort n = z | (s n)\nsort a = other \\ (f n)",
            "expected `_`",
        );
    }

    #[test]
    fn other_of_without_a_sort_rejected() {
        rejected("sort a = other of", "expected the name of a sort");
    }

    #[test]
    fn backslash_without_a_symbol_rejected() {
        rejected("sort a = other \\", "expected a symbol");
    }

    #[test]
    fn empty_index_rejected() {
        rejected("sort d() = none", "expected a pattern");
    }

    #[test]
    fn unclosed_index_rejected() {
        rejected("sort d((s $n) = none", "expected `)`");
    }

    #[test]
    fn variable_as_an_alternative_rejected() {
        rejected("sort a = $x", "expected an alternative");
    }

    #[test]
    fn dollar_without_a_name_rejected() {
        rejected("sort d($) = none", "expected the name of a variable");
    }

    #[test]
    fn unknown_character_rejected() {
        let e = rejected("sort a = b; sort c = d", "unexpected character `;`");
        assert_eq!(e.position, 10);
    }

    // ---- well-formedness ----

    #[test]
    fn wf_empty_sort() {
        assert_eq!(env("sort e = none").check_well_formed(), Ok(()));
    }

    #[test]
    fn wf_sort_of_one_term() {
        assert_eq!(env("sort one = a").check_well_formed(), Ok(()));
    }

    #[test]
    fn wf_infinite_sort() {
        assert_eq!(env(N).check_well_formed(), Ok(()));
    }

    #[test]
    fn wf_sort_of_two_constants_rejected() {
        let e = rejected(
            "sort one = a\nsort two = a | b",
            "the sort two has finitely many terms, and more than one",
        );
        assert_eq!(e.position, 13);
    }

    #[test]
    fn wf_finite_through_a_finite_argument_rejected() {
        rejected(
            "sort u = a\nsort w = (f u) | (g u)",
            "the sort w has finitely many terms, and more than one",
        );
    }

    #[test]
    fn wf_one_term_through_an_argument() {
        env("sort u = a\nsort w = (f u)");
    }

    #[test]
    fn wf_two_terms_through_two_arguments_rejected() {
        rejected(
            "sort u = a\nsort w = (f u) | u\nsort p = (g w w)",
            "the sort w has finitely many terms",
        );
    }

    #[test]
    fn wf_two_sorts_sharing_two_constants_rejected() {
        rejected(
            "sort sk = k | s | (a sk sk)\nsort kn = k | s | (succ kn)",
            "the sorts sk, kn have finitely many terms in common, and more than one",
        );
    }

    #[test]
    fn wf_two_sorts_sharing_one_constant() {
        env("sort sk = k | (a sk sk)\nsort kn = k | (succ kn)");
    }

    #[test]
    fn wf_two_sorts_sharing_nothing() {
        env("sort p = a | (f p)\nsort q = b | (g q)");
    }

    #[test]
    fn wf_sorts_with_other_symbols() {
        env("sort any = other\n\
             sort name = other \\ (app _ _) \\ (lam _ _)\n\
             sort noc = other of noc \\ (c _)");
    }

    #[test]
    fn wf_other_symbols_meeting_a_grammar_in_two_constants_rejected() {
        rejected(
            "sort p = a | b | (f p)\nsort q = other \\ (f _)",
            "the sorts p, q have finitely many terms in common",
        );
    }

    #[test]
    fn wf_sort_with_no_base_is_empty() {
        env("sort a = (f a)");
    }

    #[test]
    fn wf_dead_case_does_not_count() {
        // (g e) has no term, so `w` has the one term `a`.
        env("sort e = none\nsort w = a | (g e)");
    }

    #[test]
    fn wf_three_sorts_finite_only_together_rejected() {
        // Each pair shares infinitely many terms, all three share `a` and `b`.
        rejected(
            "sort x = a | b | (f x) | (g x)\n\
             sort y = a | b | (g y) | (h y)\n\
             sort z = a | b | (h z) | (f z)",
            "the sorts x, y, z have finitely many terms in common",
        );
    }

    #[test]
    fn wf_chain_of_larger_and_larger_sorts_is_read_quickly() {
        // 40 sorts, each inside the next: every set of them has a term in
        // common, and the check must not go through every set.
        let mut src = String::from("sort c0 = (k _)\n");
        for i in 1..40 {
            src.push_str(&format!("sort c{} = c{} | (f{} c{})\n", i, i - 1, i, i - 1));
        }
        assert_eq!(env(&src).table().len(), 40);
    }

    #[test]
    fn wf_instance_checked_when_resolved() {
        let mut e = env("sort d(z) = a | b\nsort d((s $n)) = none");
        let err = e.resolve("d", Some(&g("z"))).unwrap_err();
        assert!(
            err.message
                .contains("the sort d(z) has finitely many terms, and more than one"),
            "{}",
            err
        );
        assert!(e.table().is_empty());
        assert_eq!(e.check_well_formed(), Ok(()));
    }

    #[test]
    fn wf_instance_checked_against_the_sorts_already_declared() {
        let mut e = env("sort p = a | b | (f p)\nsort d(z) = a | b | (g d(z))");
        let err = e.resolve("d", Some(&g("z"))).unwrap_err();
        assert!(
            err.message
                .contains("the sorts p, d(z) have finitely many terms in common"),
            "{}",
            err
        );
        assert_eq!(e.table().len(), 1);
    }
}
