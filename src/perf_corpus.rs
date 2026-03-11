use crate::chr::ChrState;
use crate::engine::Engine;
use crate::parser::{ChrConstraintBuilder, Parser, RelDef};
use crate::perf_counters;
use crate::rel::Rel;
use crate::repl::split_statements;
use crate::term::TermStore;
use crate::work::Env;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::env;
use std::fs;
use std::process::Command;
use std::str::FromStr;
use std::sync::OnceLock;
use std::time::{SystemTime, UNIX_EPOCH};

pub type CorpusConstraint = ChrState;
pub const CORPUS_SCHEMA_VERSION: u32 = 1;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct EnvironmentFingerprint {
    pub os: String,
    pub arch: String,
    #[serde(default)]
    pub cpu_model: Option<String>,
    pub rustc_version: String,
    #[serde(default)]
    pub rustflags: Option<String>,
    #[serde(default)]
    pub timestamp_unix_s: u64,
    #[serde(default)]
    pub hostname: Option<String>,
    #[serde(default)]
    pub git_sha: Option<String>,
    #[serde(default)]
    pub github_run_id: Option<String>,
    #[serde(default)]
    pub github_job: Option<String>,
    #[serde(default)]
    pub github_ref: Option<String>,
    #[serde(default)]
    pub run_id: Option<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CaseCategory {
    FiniteDeterministic,
    FiniteNondeterministic,
    Recursive,
    Constraints,
    DeepTerms,
    WideBranching,
}

impl FromStr for CaseCategory {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "finite_det" => Ok(CaseCategory::FiniteDeterministic),
            "finite_nondet" => Ok(CaseCategory::FiniteNondeterministic),
            "recursive" => Ok(CaseCategory::Recursive),
            "constraints" => Ok(CaseCategory::Constraints),
            "deep_terms" => Ok(CaseCategory::DeepTerms),
            "wide_branching" => Ok(CaseCategory::WideBranching),
            other => Err(format!("unknown category '{other}'")),
        }
    }
}

impl CaseCategory {
    pub fn as_str(self) -> &'static str {
        match self {
            CaseCategory::FiniteDeterministic => "finite_det",
            CaseCategory::FiniteNondeterministic => "finite_nondet",
            CaseCategory::Recursive => "recursive",
            CaseCategory::Constraints => "constraints",
            CaseCategory::DeepTerms => "deep_terms",
            CaseCategory::WideBranching => "wide_branching",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum CaseTier {
    Quick,
    Stress,
}

impl FromStr for CaseTier {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "quick" => Ok(CaseTier::Quick),
            "stress" => Ok(CaseTier::Stress),
            other => Err(format!("unknown tier '{other}'")),
        }
    }
}

impl CaseTier {
    pub fn as_str(self) -> &'static str {
        match self {
            CaseTier::Quick => "quick",
            CaseTier::Stress => "stress",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DeterminismClass {
    Deterministic,
    Nondeterministic,
}

impl FromStr for DeterminismClass {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "deterministic" => Ok(DeterminismClass::Deterministic),
            "nondeterministic" => Ok(DeterminismClass::Nondeterministic),
            other => Err(format!("unknown determinism '{other}'")),
        }
    }
}

impl DeterminismClass {
    pub fn as_str(self) -> &'static str {
        match self {
            DeterminismClass::Deterministic => "deterministic",
            DeterminismClass::Nondeterministic => "nondeterministic",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum AnswerShape {
    Single,
    Finite,
    PrefixStream,
}

impl FromStr for AnswerShape {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "single" => Ok(AnswerShape::Single),
            "finite" => Ok(AnswerShape::Finite),
            "prefix_stream" => Ok(AnswerShape::PrefixStream),
            other => Err(format!("unknown answer shape '{other}'")),
        }
    }
}

impl AnswerShape {
    pub fn as_str(self) -> &'static str {
        match self {
            AnswerShape::Single => "single",
            AnswerShape::Finite => "finite",
            AnswerShape::PrefixStream => "prefix_stream",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RunMode {
    FirstAnswer,
    FirstN(usize),
    Exhaust,
}

impl RunMode {
    pub fn from_parts(mode: &str, mode_limit: Option<usize>) -> Self {
        match mode {
            "first_answer" => RunMode::FirstAnswer,
            "first_n" => RunMode::FirstN(mode_limit.expect("first_n requires mode_limit")),
            "exhaust" => RunMode::Exhaust,
            other => panic!("unknown mode '{other}'"),
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            RunMode::FirstAnswer => "first_answer",
            RunMode::FirstN(_) => "first_n",
            RunMode::Exhaust => "exhaust",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExpectedAnswers {
    Exact(usize),
    AtLeast(usize),
}

impl ExpectedAnswers {
    pub fn from_parts(kind: &str, value: usize) -> Self {
        match kind {
            "exact" => ExpectedAnswers::Exact(value),
            "at_least" => ExpectedAnswers::AtLeast(value),
            other => panic!("unknown expected_kind '{other}'"),
        }
    }

    pub fn as_str(self) -> String {
        match self {
            ExpectedAnswers::Exact(n) => format!("exact:{n}"),
            ExpectedAnswers::AtLeast(n) => format!("at_least:{n}"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CorpusCase {
    pub id: String,
    pub title: String,
    pub tier: CaseTier,
    pub category: CaseCategory,
    pub description: String,
    pub program: String,
    pub query: String,
    pub mode: RunMode,
    pub expected: ExpectedAnswers,
    pub tags: Vec<String>,
    pub determinism: DeterminismClass,
    pub answer_shape: AnswerShape,
    pub infinite_stream: bool,
    pub quick_gate_max_median_us: Option<f64>,
    pub quick_gate_max_p95_us: Option<f64>,
    pub noise_target_cv_pct: Option<f64>,
    pub noise_flaky_cv_pct: Option<f64>,
    pub adaptive_min_samples: Option<usize>,
    pub adaptive_max_samples: Option<usize>,
    pub notes: Option<String>,
}

#[derive(Debug, Deserialize)]
struct CorpusSpec {
    corpus: CorpusMetaRaw,
    case: Vec<CorpusCaseRaw>,
}

#[derive(Debug, Deserialize)]
struct CorpusMetaRaw {
    schema_version: u32,
    min_quick_cases: Option<usize>,
    min_stress_cases: Option<usize>,
    min_by_category: Option<BTreeMap<String, usize>>,
    require_real_world_tag_in_categories: Option<Vec<String>>,
}

#[derive(Debug, Deserialize)]
struct CorpusCaseRaw {
    id: String,
    title: String,
    tier: String,
    category: String,
    description: String,
    program: String,
    query: String,
    mode: String,
    mode_limit: Option<usize>,
    expected_kind: String,
    expected_value: usize,
    tags: Option<Vec<String>>,
    determinism: Option<String>,
    answer_shape: Option<String>,
    infinite_stream: Option<bool>,
    quick_gate_max_median_us: Option<f64>,
    quick_gate_max_p95_us: Option<f64>,
    noise_target_cv_pct: Option<f64>,
    noise_flaky_cv_pct: Option<f64>,
    adaptive_min_samples: Option<usize>,
    adaptive_max_samples: Option<usize>,
    notes: Option<String>,
}

pub struct PreparedCase {
    rel: Rel<CorpusConstraint>,
    terms: TermStore,
    env: Env<CorpusConstraint>,
}

pub type ExecutionCounters = perf_counters::PerfCountersSnapshot;

#[derive(Clone, Copy, Debug, Default)]
pub struct RunStats {
    pub answers: usize,
    pub counters: ExecutionCounters,
}

#[derive(Clone, Debug)]
pub struct CorpusMeta {
    pub schema_version: u32,
    pub min_quick_cases: usize,
    pub min_stress_cases: usize,
    pub min_by_category: BTreeMap<String, usize>,
    pub require_real_world_tag_in_categories: Vec<String>,
}

#[derive(Clone, Copy, Debug)]
pub enum TierFilter {
    All,
    Quick,
    Stress,
}

/// Filter for gate/probe data sources in history snapshots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SourceFilter {
    Gate,
    Probe,
    All,
}

impl SourceFilter {
    pub fn to_str(self) -> &'static str {
        match self {
            SourceFilter::Gate => "gate",
            SourceFilter::Probe => "probe",
            SourceFilter::All => "all",
        }
    }

    pub fn includes_gate(self) -> bool {
        matches!(self, SourceFilter::Gate | SourceFilter::All)
    }

    pub fn includes_probe(self) -> bool {
        matches!(self, SourceFilter::Probe | SourceFilter::All)
    }
}

impl std::str::FromStr for SourceFilter {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, String> {
        match s {
            "gate" => Ok(SourceFilter::Gate),
            "probe" => Ok(SourceFilter::Probe),
            "all" => Ok(SourceFilter::All),
            _ => Err(format!("Unknown source filter '{}' (expected gate|probe|all)", s)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CorpusFilters {
    pub tier: TierFilter,
    pub categories: Option<HashSet<String>>,
    pub filter_substring: Option<String>,
    pub max_cases: Option<usize>,
    pub determinism: Option<DeterminismClass>,
    pub answer_shape: Option<AnswerShape>,
    pub tag_filter: Option<HashSet<String>>,
}

impl Default for CorpusFilters {
    fn default() -> Self {
        Self {
            tier: TierFilter::All,
            categories: None,
            filter_substring: None,
            max_cases: None,
            determinism: None,
            answer_shape: None,
            tag_filter: None,
        }
    }
}

impl CorpusFilters {
    pub fn from_env() -> Self {
        let mut out = CorpusFilters::default();
        if let Some(tier) = env_var("RWLOG_CORPUS_TIER") {
            out.tier = match tier.as_str() {
                "all" => TierFilter::All,
                "quick" => TierFilter::Quick,
                "stress" => TierFilter::Stress,
                other => panic!("RWLOG_CORPUS_TIER must be quick|stress|all, got '{other}'"),
            };
        }
        if let Some(category_filter) = env_var("RWLOG_CORPUS_CATEGORY") {
            let wanted: HashSet<String> = category_filter
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            out.categories = Some(wanted);
        }
        if let Some(filter) = env_var("RWLOG_CORPUS_FILTER") {
            out.filter_substring = Some(filter);
        }
        if let Some(max_cases) = env_var("RWLOG_CORPUS_MAX_CASES") {
            out.max_cases = Some(
                max_cases
                    .parse()
                    .expect("RWLOG_CORPUS_MAX_CASES must be integer"),
            );
        }
        if let Some(d) = env_var("RWLOG_CORPUS_DETERMINISM") {
            out.determinism = Some(d.parse().expect("valid RWLOG_CORPUS_DETERMINISM"));
        }
        if let Some(shape) = env_var("RWLOG_CORPUS_ANSWER_SHAPE") {
            out.answer_shape = Some(shape.parse().expect("valid RWLOG_CORPUS_ANSWER_SHAPE"));
        }
        if let Some(tags) = env_var("RWLOG_CORPUS_TAGS") {
            let wanted: HashSet<String> = tags
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            out.tag_filter = Some(wanted);
        }
        out
    }
}

pub fn load_cases() -> Vec<CorpusCase> {
    let (_meta, cases) = load_meta_and_cases();
    cases
}

pub fn environment_fingerprint() -> EnvironmentFingerprint {
    static FP: OnceLock<EnvironmentFingerprint> = OnceLock::new();
    FP.get_or_init(build_environment_fingerprint).clone()
}

pub fn load_meta_and_cases() -> (CorpusMeta, Vec<CorpusCase>) {
    let raw: CorpusSpec =
        toml::from_str(include_str!("../benches/perf_corpus_cases.toml")).expect("parse corpus");
    let meta = normalize_meta(raw.corpus);

    let mut cases = Vec::with_capacity(raw.case.len());
    for c in raw.case {
        let case = CorpusCase {
            id: c.id,
            title: c.title,
            tier: c.tier.parse().expect("valid tier"),
            category: c.category.parse().expect("valid category"),
            description: c.description,
            program: expand_templates(&c.program),
            query: expand_templates(&c.query),
            mode: RunMode::from_parts(&c.mode, c.mode_limit),
            expected: ExpectedAnswers::from_parts(&c.expected_kind, c.expected_value),
            tags: c.tags.unwrap_or_default(),
            determinism: c
                .determinism
                .as_deref()
                .map(|s| s.parse().expect("valid determinism"))
                .unwrap_or(DeterminismClass::Nondeterministic),
            answer_shape: c
                .answer_shape
                .as_deref()
                .map(|s| s.parse().expect("valid answer_shape"))
                .unwrap_or(AnswerShape::Finite),
            infinite_stream: c.infinite_stream.unwrap_or(false),
            quick_gate_max_median_us: c.quick_gate_max_median_us,
            quick_gate_max_p95_us: c.quick_gate_max_p95_us,
            noise_target_cv_pct: c.noise_target_cv_pct,
            noise_flaky_cv_pct: c.noise_flaky_cv_pct,
            adaptive_min_samples: c.adaptive_min_samples,
            adaptive_max_samples: c.adaptive_max_samples,
            notes: c.notes,
        };
        cases.push(case);
    }
    lint_cases_with_meta(&meta, &cases).expect("corpus lint checks");
    (meta, cases)
}

fn normalize_meta(raw: CorpusMetaRaw) -> CorpusMeta {
    CorpusMeta {
        schema_version: raw.schema_version,
        min_quick_cases: raw.min_quick_cases.unwrap_or(1),
        min_stress_cases: raw.min_stress_cases.unwrap_or(1),
        min_by_category: raw.min_by_category.unwrap_or_default(),
        require_real_world_tag_in_categories: raw
            .require_real_world_tag_in_categories
            .unwrap_or_default(),
    }
}

pub fn apply_filters(mut cases: Vec<CorpusCase>, filters: &CorpusFilters) -> Vec<CorpusCase> {
    cases.retain(|c| match filters.tier {
        TierFilter::All => true,
        TierFilter::Quick => c.tier == CaseTier::Quick,
        TierFilter::Stress => c.tier == CaseTier::Stress,
    });
    if let Some(categories) = &filters.categories {
        cases.retain(|c| categories.contains(c.category.as_str()));
    }
    if let Some(filter) = &filters.filter_substring {
        cases.retain(|c| c.id.contains(filter) || c.title.contains(filter));
    }
    if let Some(det) = filters.determinism {
        cases.retain(|c| c.determinism == det);
    }
    if let Some(shape) = filters.answer_shape {
        cases.retain(|c| c.answer_shape == shape);
    }
    if let Some(tags) = &filters.tag_filter {
        cases.retain(|c| c.tags.iter().any(|tag| tags.contains(tag)));
    }
    if let Some(max_cases) = filters.max_cases {
        cases.truncate(max_cases);
    }
    cases
}

pub fn sort_cases(cases: &mut [CorpusCase]) {
    cases.sort_by(|a, b| {
        (a.tier, a.category, a.determinism, &a.id).cmp(&(b.tier, b.category, b.determinism, &b.id))
    });
}

pub fn lint_cases(cases: &[CorpusCase]) -> Result<(), String> {
    // Full corpus policy is already validated by load_meta_and_cases() (called by load_cases()).
    // Only validate per-row invariants for the given subset.
    lint_case_rows(cases)
}

pub fn lint_full_corpus() -> Result<String, String> {
    let (meta, cases) = load_meta_and_cases();
    lint_cases_with_meta(&meta, &cases)?;
    Ok(corpus_meta_summary(&meta, &cases))
}

fn lint_cases_with_meta(meta: &CorpusMeta, cases: &[CorpusCase]) -> Result<(), String> {
    if meta.schema_version != CORPUS_SCHEMA_VERSION {
        return Err(format!(
            "unsupported corpus schema version {} (expected {})",
            meta.schema_version, CORPUS_SCHEMA_VERSION
        ));
    }
    for category in meta.min_by_category.keys() {
        category.parse::<CaseCategory>()?;
    }
    for category in &meta.require_real_world_tag_in_categories {
        category.parse::<CaseCategory>()?;
    }

    lint_case_rows(cases)?;
    lint_coverage(meta, cases)?;
    Ok(())
}

fn lint_case_rows(cases: &[CorpusCase]) -> Result<(), String> {
    let mut ids = BTreeSet::new();
    for case in cases {
        if case.id.trim().is_empty() {
            return Err("case id must be non-empty".to_string());
        }
        if !ids.insert(case.id.clone()) {
            return Err(format!("duplicate case id '{}'", case.id));
        }
        if case.title.trim().is_empty() {
            return Err(format!("case '{}' has empty title", case.id));
        }
        if case.description.trim().is_empty() {
            return Err(format!("case '{}' has empty description", case.id));
        }
        if case.query.trim().is_empty() {
            return Err(format!("case '{}' has empty query", case.id));
        }
        if case.tags.is_empty() {
            return Err(format!("case '{}' must have at least one tag", case.id));
        }
        let has_median = case.quick_gate_max_median_us.is_some();
        let has_p95 = case.quick_gate_max_p95_us.is_some();
        let has_noise_target = case.noise_target_cv_pct.is_some();
        let has_noise_flaky = case.noise_flaky_cv_pct.is_some();
        let has_adaptive_min = case.adaptive_min_samples.is_some();
        let has_adaptive_max = case.adaptive_max_samples.is_some();
        if has_median != has_p95 {
            return Err(format!(
                "case '{}' must set both quick_gate_max_median_us and quick_gate_max_p95_us together",
                case.id
            ));
        }
        if has_noise_target != has_noise_flaky {
            return Err(format!(
                "case '{}' must set both noise_target_cv_pct and noise_flaky_cv_pct together",
                case.id
            ));
        }
        if has_adaptive_min != has_adaptive_max {
            return Err(format!(
                "case '{}' must set both adaptive_min_samples and adaptive_max_samples together",
                case.id
            ));
        }
        if case.tier == CaseTier::Quick {
            match (case.quick_gate_max_median_us, case.quick_gate_max_p95_us) {
                (Some(median), Some(p95)) => {
                    if !(median.is_finite() && p95.is_finite() && median > 0.0 && p95 > 0.0) {
                        return Err(format!(
                            "case '{}' quick gate thresholds must be finite and > 0",
                            case.id
                        ));
                    }
                }
                _ => {
                    return Err(format!(
                        "case '{}' is quick tier and must define quick gate thresholds",
                        case.id
                    ));
                }
            }
            if let Some(target_cv_pct) = case.noise_target_cv_pct {
                if !(target_cv_pct.is_finite() && target_cv_pct > 0.0) {
                    return Err(format!(
                        "case '{}' noise_target_cv_pct must be finite and > 0",
                        case.id
                    ));
                }
            }
            if let Some(flaky_cv_pct) = case.noise_flaky_cv_pct {
                if !(flaky_cv_pct.is_finite() && flaky_cv_pct > 0.0) {
                    return Err(format!(
                        "case '{}' noise_flaky_cv_pct must be finite and > 0",
                        case.id
                    ));
                }
            }
            if let (Some(target_cv_pct), Some(flaky_cv_pct)) =
                (case.noise_target_cv_pct, case.noise_flaky_cv_pct)
            {
                if flaky_cv_pct < target_cv_pct {
                    return Err(format!(
                        "case '{}' noise_flaky_cv_pct ({}) must be >= noise_target_cv_pct ({})",
                        case.id, flaky_cv_pct, target_cv_pct
                    ));
                }
            }
            if let Some(min_samples) = case.adaptive_min_samples {
                if min_samples == 0 {
                    return Err(format!(
                        "case '{}' adaptive_min_samples must be > 0",
                        case.id
                    ));
                }
            }
            if let Some(max_samples) = case.adaptive_max_samples {
                if max_samples == 0 {
                    return Err(format!(
                        "case '{}' adaptive_max_samples must be > 0",
                        case.id
                    ));
                }
            }
            if let (Some(min_samples), Some(max_samples)) =
                (case.adaptive_min_samples, case.adaptive_max_samples)
            {
                if max_samples < min_samples {
                    return Err(format!(
                        "case '{}' adaptive_max_samples ({}) must be >= adaptive_min_samples ({})",
                        case.id, max_samples, min_samples
                    ));
                }
            }
        } else if has_median || has_p95 {
            return Err(format!(
                "case '{}' is stress tier and must not define quick gate thresholds",
                case.id
            ));
        } else if has_noise_target || has_noise_flaky || has_adaptive_min || has_adaptive_max {
            return Err(format!(
                "case '{}' is stress tier and must not define quick-only noise/adaptive fields",
                case.id
            ));
        }
        if case.infinite_stream && matches!(case.mode, RunMode::Exhaust) {
            return Err(format!(
                "case '{}' marks infinite_stream=true but mode=exhaust",
                case.id
            ));
        }
        if case.infinite_stream && case.answer_shape != AnswerShape::PrefixStream {
            return Err(format!(
                "case '{}' infinite_stream=true requires answer_shape=prefix_stream",
                case.id
            ));
        }
        if case.determinism == DeterminismClass::Deterministic
            && !matches!(case.expected, ExpectedAnswers::Exact(_))
        {
            return Err(format!(
                "case '{}' deterministic cases must use expected_kind=exact",
                case.id
            ));
        }
        if let RunMode::FirstN(limit) = case.mode {
            if limit == 0 {
                return Err(format!(
                    "case '{}' first_n requires mode_limit > 0",
                    case.id
                ));
            }
            if let ExpectedAnswers::Exact(n) = case.expected {
                if n > limit {
                    return Err(format!(
                        "case '{}' has expected exact {} > first_n limit {}",
                        case.id, n, limit
                    ));
                }
            }
        }
    }
    Ok(())
}

fn lint_coverage(meta: &CorpusMeta, cases: &[CorpusCase]) -> Result<(), String> {
    let quick = cases.iter().filter(|c| c.tier == CaseTier::Quick).count();
    let stress = cases.iter().filter(|c| c.tier == CaseTier::Stress).count();
    if quick < meta.min_quick_cases {
        return Err(format!(
            "quick tier has {} cases, requires at least {}",
            quick, meta.min_quick_cases
        ));
    }
    if stress < meta.min_stress_cases {
        return Err(format!(
            "stress tier has {} cases, requires at least {}",
            stress, meta.min_stress_cases
        ));
    }

    let mut by_category: BTreeMap<String, usize> = BTreeMap::new();
    for case in cases {
        *by_category
            .entry(case.category.as_str().to_string())
            .or_insert(0) += 1;
    }
    for (category, min_count) in &meta.min_by_category {
        let got = by_category.get(category).copied().unwrap_or(0);
        if got < *min_count {
            return Err(format!(
                "category '{}' has {} cases, requires at least {}",
                category, got, min_count
            ));
        }
    }

    for category in &meta.require_real_world_tag_in_categories {
        let found = cases.iter().any(|c| {
            c.category.as_str() == category && c.tags.iter().any(|tag| tag == "realistic")
        });
        if !found {
            return Err(format!(
                "category '{}' must include at least one case tagged 'realistic'",
                category
            ));
        }
    }
    Ok(())
}

fn corpus_meta_summary(meta: &CorpusMeta, cases: &[CorpusCase]) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        "schema_version={} (expected {})\n",
        meta.schema_version, CORPUS_SCHEMA_VERSION
    ));
    out.push_str(&format!(
        "policy: min_quick_cases={} min_stress_cases={}\n",
        meta.min_quick_cases, meta.min_stress_cases
    ));
    if meta.min_by_category.is_empty() {
        out.push_str("policy: min_by_category=-\n");
    } else {
        let mut entries: Vec<String> = Vec::new();
        for (k, v) in &meta.min_by_category {
            entries.push(format!("{k}:{v}"));
        }
        out.push_str(&format!("policy: min_by_category={}\n", entries.join(",")));
    }
    if meta.require_real_world_tag_in_categories.is_empty() {
        out.push_str("policy: require_realistic_categories=-\n");
    } else {
        out.push_str(&format!(
            "policy: require_realistic_categories={}\n",
            meta.require_real_world_tag_in_categories.join(",")
        ));
    }
    out.push_str(&format!("cases_total={}\n", cases.len()));
    out
}

pub fn summary_string(cases: &[CorpusCase], filters: &CorpusFilters) -> String {
    let mut by_tier: BTreeMap<CaseTier, usize> = BTreeMap::new();
    let mut by_category: BTreeMap<CaseCategory, usize> = BTreeMap::new();
    let mut by_det: BTreeMap<&'static str, usize> = BTreeMap::new();
    for c in cases {
        *by_tier.entry(c.tier).or_insert(0) += 1;
        *by_category.entry(c.category).or_insert(0) += 1;
        *by_det.entry(c.determinism.as_str()).or_insert(0) += 1;
    }
    let mut out = String::new();
    out.push_str("== rwlog performance corpus ==\n");
    out.push_str(&format!(
        "selected_cases={} tier={} category={} filter={} max_cases={} determinism={} answer_shape={} tags={}\n",
        cases.len(),
        match filters.tier {
            TierFilter::All => "all",
            TierFilter::Quick => "quick",
            TierFilter::Stress => "stress",
        },
        filters
            .categories
            .as_ref()
            .map(|s| {
                let mut v: Vec<_> = s.iter().cloned().collect();
                v.sort();
                v.join(",")
            })
            .unwrap_or_else(|| "-".to_string()),
        filters.filter_substring.as_deref().unwrap_or("-"),
        filters
            .max_cases
            .map(|n| n.to_string())
            .unwrap_or_else(|| "-".to_string()),
        filters
            .determinism
            .map(|d| d.as_str().to_string())
            .unwrap_or_else(|| "-".to_string()),
        filters
            .answer_shape
            .map(|s| s.as_str().to_string())
            .unwrap_or_else(|| "-".to_string()),
        filters
            .tag_filter
            .as_ref()
            .map(|s| {
                let mut v: Vec<_> = s.iter().cloned().collect();
                v.sort();
                v.join(",")
            })
            .unwrap_or_else(|| "-".to_string()),
    ));
    for (tier, count) in by_tier {
        out.push_str(&format!("tier/{}={}\n", tier.as_str(), count));
    }
    for (category, count) in by_category {
        out.push_str(&format!("category/{}={}\n", category.as_str(), count));
    }
    for (det, count) in by_det {
        out.push_str(&format!("determinism/{}={}\n", det, count));
    }
    out.push_str("-- case inventory --\n");
    for c in cases {
        let tags = if c.tags.is_empty() {
            "-".to_string()
        } else {
            c.tags.join(",")
        };
        out.push_str(&format!(
            "{} | {} | {} | {} | {} | det={} | shape={} | stream={} | gate={}/{} | noise_cv={}/{} | adaptive_samples={}/{} | tags={} | {}\n",
            c.id,
            c.tier.as_str(),
            c.category.as_str(),
            c.mode.as_str(),
            c.expected.as_str(),
            c.determinism.as_str(),
            c.answer_shape.as_str(),
            c.infinite_stream,
            c.quick_gate_max_median_us
                .map(|v| format!("{v:.1}"))
                .unwrap_or_else(|| "-".to_string()),
            c.quick_gate_max_p95_us
                .map(|v| format!("{v:.1}"))
                .unwrap_or_else(|| "-".to_string()),
            c.noise_target_cv_pct
                .map(|v| format!("{v:.1}%"))
                .unwrap_or_else(|| "-".to_string()),
            c.noise_flaky_cv_pct
                .map(|v| format!("{v:.1}%"))
                .unwrap_or_else(|| "-".to_string()),
            c.adaptive_min_samples
                .map(|v| v.to_string())
                .unwrap_or_else(|| "-".to_string()),
            c.adaptive_max_samples
                .map(|v| v.to_string())
                .unwrap_or_else(|| "-".to_string()),
            tags,
            c.description
        ));
    }
    out
}

pub fn prepare_case(case: &CorpusCase) -> PreparedCase {
    let mut parser = Parser::with_chr();
    let defs = parse_program_defs(&mut parser, &case.program);
    let rel = parser.parse_rel_body(&case.query).expect("parse query");
    let env = build_env(&defs);
    let terms = parser.take_terms();
    PreparedCase { rel, terms, env }
}

fn run_prepared_inner(case: &CorpusCase, prepared: PreparedCase) -> usize {
    let mut engine = Engine::new_with_env(prepared.rel, prepared.terms, prepared.env);
    match case.mode {
        RunMode::FirstAnswer => {
            if engine.next().is_some() {
                1
            } else {
                0
            }
        }
        RunMode::FirstN(limit) => {
            let mut count = 0usize;
            while count < limit {
                if engine.next().is_some() {
                    count += 1;
                } else {
                    break;
                }
            }
            count
        }
        RunMode::Exhaust => engine.count_answers(),
    }
}

pub fn run_prepared_with_stats(case: &CorpusCase, prepared: PreparedCase) -> RunStats {
    let (answers, counters) = perf_counters::capture(|| run_prepared_inner(case, prepared));
    RunStats { answers, counters }
}

pub fn run_prepared(case: &CorpusCase, prepared: PreparedCase) -> usize {
    run_prepared_inner(case, prepared)
}

/// Look up a single corpus case by ID, bypassing environment filters.
pub fn get_case(id: &str) -> CorpusCase {
    load_cases()
        .into_iter()
        .find(|c| c.id == id)
        .unwrap_or_else(|| panic!("corpus case '{}' not found", id))
}

/// Load cases, apply env filters with optional ID filter, sort, and panic on empty.
pub fn select_cases(id_filter: Option<String>) -> Vec<CorpusCase> {
    let mut filters = CorpusFilters::from_env();
    if let Some(id) = id_filter {
        filters.filter_substring = Some(id);
    }
    let mut cases = apply_filters(load_cases(), &filters);
    sort_cases(&mut cases);
    if cases.is_empty() {
        panic!("no corpus cases selected");
    }
    cases
}

/// Escape a string for CSV output.
pub fn csv_escape(s: &str) -> String {
    if s.contains(',') || s.contains('"') || s.contains('\n') {
        format!("\"{}\"", s.replace('"', "\"\""))
    } else {
        s.to_string()
    }
}

/// Escape an optional string for CSV output.
pub fn csv_escape_opt(s: Option<&str>) -> String {
    match s {
        Some(v) => csv_escape(v),
        None => String::new(),
    }
}

/// Mean of a slice of f64 values.
pub fn stats_mean(values: &[f64]) -> f64 {
    values.iter().sum::<f64>() / (values.len() as f64)
}

/// Sample standard deviation (Bessel-corrected, divides by N-1).
pub fn stats_stddev(values: &[f64]) -> f64 {
    if values.len() < 2 {
        return 0.0;
    }
    let m = stats_mean(values);
    let var = values
        .iter()
        .map(|v| {
            let d = v - m;
            d * d
        })
        .sum::<f64>()
        / (values.len() - 1) as f64;
    var.sqrt()
}

/// Median of a pre-sorted f64 slice.
pub fn stats_median_sorted(sorted: &[f64]) -> f64 {
    debug_assert!(
        sorted.windows(2).all(|w| w[0] <= w[1]),
        "stats_median_sorted requires sorted input"
    );
    sorted[sorted.len() / 2]
}

/// Median of a mutable u64 slice (sorts in place).
pub fn stats_median_u64(values: &mut [u64]) -> u64 {
    values.sort_unstable();
    values[values.len() / 2]
}

/// Percentile of a pre-sorted f64 slice (p in 0.0..=1.0).
pub fn stats_percentile(sorted: &[f64], p: f64) -> f64 {
    let idx = ((sorted.len() as f64) * p).ceil() as usize - 1;
    sorted[idx.min(sorted.len() - 1)]
}

/// Coefficient of variation as a percentage.
pub fn stats_cv_pct(values: &[f64]) -> f64 {
    if values.len() < 2 {
        return 0.0;
    }
    let m = stats_mean(values);
    if m <= 0.0 {
        return 0.0;
    }
    (stats_stddev(values) / m) * 100.0
}

/// Median absolute deviation as a percentage of the median.
pub fn stats_mad_pct(sorted: &[f64]) -> f64 {
    if sorted.is_empty() {
        return 0.0;
    }
    let median = stats_median_sorted(sorted);
    if median <= 0.0 {
        return 0.0;
    }
    let mut abs_dev: Vec<f64> = sorted.iter().map(|v| (v - median).abs()).collect();
    abs_dev.sort_by(|a, b| a.partial_cmp(b).expect("finite float"));
    (stats_median_sorted(&abs_dev) / median) * 100.0
}

/// 95% CI half-width as a percentage of the mean.
pub fn stats_ci95_halfwidth_pct(values: &[f64]) -> f64 {
    if values.len() < 2 {
        return 0.0;
    }
    let m = stats_mean(values);
    if m <= 0.0 {
        return 0.0;
    }
    let se = stats_stddev(values) / (values.len() as f64).sqrt();
    ((1.96 * se) / m) * 100.0
}

/// Pearson correlation coefficient between two series.
///
/// Returns None if the series have different lengths, fewer than 2 points,
/// or if either series has zero variance.
pub fn pearson_corr(xs: &[f64], ys: &[f64]) -> Option<f64> {
    if xs.len() != ys.len() || xs.len() < 2 {
        return None;
    }
    let mx = stats_mean(xs);
    let my = stats_mean(ys);
    let mut num = 0.0;
    let mut den_x = 0.0;
    let mut den_y = 0.0;
    for (x, y) in xs.iter().zip(ys.iter()) {
        let dx = x - mx;
        let dy = y - my;
        num += dx * dy;
        den_x += dx * dx;
        den_y += dy * dy;
    }
    let den = (den_x * den_y).sqrt();
    if den == 0.0 {
        return None;
    }
    Some(num / den)
}

// ---------------------------------------------------------------------------
// History snapshot types and loading (for reading gate/probe JSON output)
// ---------------------------------------------------------------------------

/// A single row in a history snapshot (gate or probe).
#[derive(Clone, Debug, Deserialize)]
pub struct SnapshotRow {
    pub id: String,
    pub median_us: f64,
    pub p95_us: f64,
}

/// A report from a history snapshot (gate or probe).
#[derive(Clone, Debug, Deserialize)]
pub struct SnapshotReport {
    #[serde(default)]
    pub environment: Option<EnvironmentFingerprint>,
    pub rows: Vec<SnapshotRow>,
}

/// A single history snapshot directory containing gate and/or probe results.
#[derive(Clone, Debug)]
pub struct PerfSnapshot {
    pub name: String,
    pub gate: Option<SnapshotReport>,
    pub probe: Option<SnapshotReport>,
}

/// Load and deserialize a JSON file, returning None on any error.
pub fn load_json<T: for<'de> Deserialize<'de>>(path: &std::path::Path) -> Option<T> {
    let text = fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

/// Load a single history snapshot from a directory.
pub fn load_snapshot(dir: &std::path::Path) -> Option<PerfSnapshot> {
    let name = dir.file_name()?.to_str()?.to_string();
    let gate = load_json::<SnapshotReport>(&dir.join("gate.json"))
        .or_else(|| load_json::<SnapshotReport>(&dir.join("quick_gate.json")));
    let probe = load_json::<SnapshotReport>(&dir.join("probe.json"))
        .or_else(|| load_json::<SnapshotReport>(&dir.join("quick_probe.json")))
        .or_else(|| load_json::<SnapshotReport>(&dir.join("stress_probe.json")));
    if gate.is_none() && probe.is_none() {
        return None;
    }
    Some(PerfSnapshot { name, gate, probe })
}

/// Load all history snapshots from a directory, sorted by name.
pub fn load_snapshots(history_dir: &std::path::Path) -> Vec<PerfSnapshot> {
    let entries = fs::read_dir(history_dir)
        .unwrap_or_else(|e| panic!("read_dir {}: {}", history_dir.display(), e));
    let mut dirs = Vec::new();
    for entry in entries {
        let entry = entry.expect("dir entry");
        let path = entry.path();
        if path.is_dir() {
            dirs.push(path);
        }
    }
    dirs.sort();
    let mut snapshots = Vec::new();
    for dir in dirs {
        if let Some(s) = load_snapshot(&dir) {
            snapshots.push(s);
        }
    }
    snapshots
}

/// Load snapshots, keeping only the last `window` entries (or all if None).
pub fn load_snapshots_windowed(
    dir: &std::path::Path,
    window: Option<usize>,
) -> Vec<PerfSnapshot> {
    if !dir.exists() {
        panic!("History directory not found: {}", dir.display());
    }
    let mut snapshots = load_snapshots(dir);
    if snapshots.is_empty() {
        panic!("No snapshots found in {}", dir.display());
    }
    if let Some(w) = window {
        if snapshots.len() > w {
            let keep_from = snapshots.len() - w;
            snapshots = snapshots.split_off(keep_from);
        }
    }
    snapshots
}

pub fn validate_case(case: &CorpusCase) -> Result<(), String> {
    let got = run_prepared(case, prepare_case(case));
    match case.expected {
        ExpectedAnswers::Exact(n) => {
            if got != n {
                Err(format!(
                    "case '{}' expected exactly {} answers, got {}",
                    case.id, n, got
                ))
            } else {
                Ok(())
            }
        }
        ExpectedAnswers::AtLeast(n) => {
            if got < n {
                Err(format!(
                    "case '{}' expected at least {} answers, got {}",
                    case.id, n, got
                ))
            } else {
                Ok(())
            }
        }
    }
}

pub fn validate_cases(cases: &[CorpusCase]) -> Result<(), String> {
    for case in cases {
        validate_case(case)?;
    }
    Ok(())
}

pub fn case_bench_id(case: &CorpusCase) -> String {
    format!(
        "{}/{}/{}",
        case.tier.as_str(),
        case.category.as_str(),
        case.id
    )
}

fn parse_program_defs(
    parser: &mut Parser<ChrConstraintBuilder>,
    program: &str,
) -> HashMap<String, Rel<CorpusConstraint>> {
    let mut defs = HashMap::new();
    let statements = split_statements(program).expect("split program statements");
    for statement in statements {
        let line = statement.trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with("theory ") {
            parser.parse_theory_def(line).expect("parse theory");
            defs.clear();
            continue;
        }
        if line.starts_with("rel ") {
            if let RelDef::Relation(name, rel) = parser.parse_rel_def(line).expect("parse relation") {
                defs.insert(name, rel);
            }
            continue;
        }
        panic!("unsupported corpus statement: {line}");
    }
    defs
}

fn build_env(defs: &HashMap<String, Rel<CorpusConstraint>>) -> Env<CorpusConstraint> {
    Env::from_defs(defs)
}

pub fn peano(n: usize) -> String {
    if n == 0 {
        "z".to_string()
    } else {
        format!("(s {})", peano(n - 1))
    }
}

fn nested(term: &str, depth: usize) -> String {
    let mut out = term.to_string();
    for _ in 0..depth {
        out = format!("(f {out})");
    }
    out
}

fn or_program(branches: usize) -> String {
    let mut rules = Vec::with_capacity(branches);
    for i in 0..branches {
        rules.push(format!("a -> (tag{i} a)"));
    }
    format!("rel wide_or {{\n{}\n}}", rules.join("\n|\n"))
}

fn chain_program(len: usize) -> String {
    assert!(len >= 1);
    let mut defs = String::new();
    for i in 0..len {
        let lhs = format!("v{i}");
        let rhs = format!("v{}", i + 1);
        defs.push_str(&format!("rel r{i} {{ {lhs} -> {rhs} }}\n"));
    }
    defs
}

fn chain_query(len: usize) -> String {
    assert!(len >= 1);
    let mut query = "@v0".to_string();
    for i in 0..len {
        query.push_str(&format!(" ; r{i}"));
    }
    query
}

fn add_program() -> &'static str {
    r#"
rel add {
    (cons z $y) -> $y
    |
    [(cons (s $x) $y) -> (cons $x $y) ; add ; $z -> (s $z)]
}
"#
}

fn even_odd_program() -> &'static str {
    r#"
rel even {
    z -> yes
    |
    [(s $n) -> $n ; odd]
}

rel odd {
    z -> no
    |
    [(s $n) -> $n ; even]
}
"#
}

fn eq_neq_program() -> &'static str {
    r#"
theory eq_neq {
    constraint eq/2
    constraint neq/2
    constraint nonzero/1

    (eq $x $x) <=> .
    (eq z (s $x)) <=> fail.
    (eq (s $x) z) <=> fail.
    (eq (s $x) (s $y)) <=> (eq $x $y).

    (neq $x $x) <=> fail.
    (neq z (s $x)) <=> .
    (neq (s $x) z) <=> .
    (neq (s $x) (s $y)) <=> (neq $x $y).

    (eq $x $y), (neq $x $y) <=> fail.
    (nonzero $x) <=> (eq $x z) | fail.
    (nonzero $x) <=> (neq $x z) | true.
}

rel nonzero_ok {
    $x { (nonzero $x) } -> $x
}
"#
}

fn range_program() -> &'static str {
    r#"
theory ranges {
    constraint lt/2
    constraint leq/2
    constraint between/2

    (leq $x $x) <=> .
    (leq z $y) <=> .
    (leq (s $x) (s $y)) <=> (leq $x $y).
    (leq (s $x) z) <=> fail.

    (lt z (s $y)) <=> .
    (lt (s $x) (s $y)) <=> (lt $x $y).
    (lt $x z) <=> fail.

    (between $x (range (closed $lo) (closed $hi))) <=> (leq $lo $x), (leq $x $hi).
}

rel member {
    (pair $x $range) { (between $x $range) } -> $x
}
"#
}

fn peel_program() -> &'static str {
    "rel peel { (f $x) -> $x }"
}

fn dispatch_program(n_rules: usize) -> String {
    let mut rules = Vec::with_capacity(n_rules);
    for i in 0..n_rules {
        rules.push(format!("(c{i} $x) -> (c{i} $x)"));
    }
    format!("rel dispatch {{\n{}\n}}", rules.join("\n|\n"))
}

fn dispatch_chain_query(n_calls: usize) -> String {
    let mut query = "@(c0 a)".to_string();
    for _ in 0..n_calls {
        query.push_str(" ; dispatch");
    }
    query
}

fn many_tiny_rels_program(n: usize) -> String {
    let mut defs = Vec::with_capacity(n);
    for i in 0..n {
        defs.push(format!("rel step{i} {{ $x -> (s{i} $x) }}"));
    }
    defs.join("\n")
}

fn many_tiny_rels_query(n: usize) -> String {
    let mut parts = vec!["@a".to_string()];
    for i in 0..n {
        parts.push(format!("step{i}"));
    }
    parts.join(" ; ")
}

fn wide_match_program(n: usize) -> String {
    let mut rules = Vec::with_capacity(n);
    for i in 0..n {
        rules.push(format!("(pair (c{i} $x) a) -> (r{i} $x)"));
    }
    format!("rel wide_match {{\n{}\n}}", rules.join("\n|\n"))
}

fn nonlinear_match_program(n: usize) -> String {
    let mut rules = Vec::with_capacity(n);
    for i in 0..n {
        rules.push(format!("(pair (c{i} $x) (c{i} $x)) -> (r{i} $x)"));
    }
    format!("rel nonlinear_match {{\n{}\n}}", rules.join("\n|\n"))
}

fn wide_inc_program() -> &'static str {
    r#"
rel wide_inc {
    (t a a a a a a a a) -> (t (s a) (s a) (s a) (s a) (s a) (s a) (s a) (s a))
    | [(t (f $x0) (f $x1) (f $x2) (f $x3) (f $x4) (f $x5) (f $x6) (f $x7)) ->
        (t $x0 $x1 $x2 $x3 $x4 $x5 $x6 $x7) ;
        wide_inc ;
        (t $y0 $y1 $y2 $y3 $y4 $y5 $y6 $y7) ->
        (t (f $y0) (f $y1) (f $y2) (f $y3) (f $y4) (f $y5) (f $y6) (f $y7))]
}
"#
}

fn wide_term(width: usize, depth: usize) -> String {
    let branch = nested("a", depth);
    let branches: Vec<&str> = (0..width).map(|_| branch.as_str()).collect();
    format!("(t {})", branches.join(" "))
}

pub(crate) fn treecalc_program() -> &'static str {
    r#"rel app {
    (f l $z) -> (b $z)
    |
    (f (b $y) $z) -> (f $y $z)
    |
    (f (f l $y) $z) -> $y
    |
    (f (f (f $w $x) $y) l) -> $w
    |
    [
        [(f (f (b $x) $y) $z) -> (f $x $z) ; app ; $x -> (f $x $y)]
        &
        [(f (f (b $x) $y) $z) -> (f $y $z) ; app ; $y -> (f $x $y)]
        ; app
    ]
    |
    [
        (f (f (f $w $x) $y) (b $u)) -> (f $x $u)
        ; app
    ]
    |
    [
        (f (f (f $w $x) $y) (f $u $v)) -> (f (f $y $u) $v)
        ;
        [(f (f $a $b) $c) -> (f $a $b) ; app ; $a -> (f $a $b)]
        &
        (f (f $a $b) $c) -> (f $d $c)
        ; app
    ]
}"#
}

fn treecalc_synth_program() -> &'static str {
    r#"theory treecalc_constraints {
    constraint no_c/1
    (no_c l) <=> .
    (no_c (b $x)) <=> (no_c $x).
    (no_c (f $x $y)) <=> (no_c $x), (no_c $y).
    (no_c (c $n)) <=> fail.
    (no_c (a $n $m)) <=> fail.
}

rel app {
    (f l $z) -> (b $z)
    |
    (f (b $y) $z) -> (f $y $z)
    |
    (f (f l $y) $z) -> $y
    |
    (f (f (f $w $x) $y) l) -> $w
    |
    [
        [(f (f (b $x) $y) $z) -> (f $x $z) ; app ; $x -> (f $x $y)]
        &
        [(f (f (b $x) $y) $z) -> (f $y $z) ; app ; $y -> (f $x $y)]
        ; app
    ]
    |
    [
        (f (f (f $w $x) $y) (b $u)) -> (f $x $u)
        ; app
    ]
    |
    [
        (f (f (f $w $x) $y) (f $u $v)) -> (f (f $y $u) $v)
        ;
        [(f (f $a $b) $c) -> (f $a $b) ; app ; $a -> (f $a $b)]
        &
        (f (f $a $b) $c) -> (f $d $c)
        ; app
    ]
    |
    (f (c $x) $y) -> (a (c $x) $y)
    |
    (f (a $x $y) $z) -> (a (a $x $y) $z)
}"#
}

fn graph_reach_program(n: usize) -> String {
    assert!(n >= 2);
    let mut edges = Vec::with_capacity(n - 1);
    for i in 0..n - 1 {
        edges.push(format!("n{i} -> n{}", i + 1));
    }
    format!(
        "rel edge {{\n{}\n}}\n\nrel reach {{ $x -> $x | [$x -> $x ; edge ; reach] }}",
        edges.join("\n|\n")
    )
}

fn left_rec_program(n: usize) -> String {
    let mut rules = Vec::with_capacity(n + 1);
    rules.push("a -> b0".to_string());
    for i in 0..n {
        rules.push(format!("[a -> a ; left_rec ; b{i} -> b{}]", i + 1));
    }
    format!("rel left_rec {{\n{}\n}}", rules.join("\n|\n"))
}

fn join_program(left_n: usize, right_n: usize, overlap: usize) -> String {
    assert!(overlap <= left_n && overlap <= right_n);
    let mut left_rules = Vec::with_capacity(left_n);
    for i in 0..left_n {
        left_rules.push(format!("a -> k{i}"));
    }
    let right_start = left_n - overlap;
    let mut right_rules = Vec::with_capacity(right_n);
    for i in 0..right_n {
        right_rules.push(format!("a -> k{}", right_start + i));
    }
    format!(
        "rel left_gen {{\n{}\n}}\n\nrel right_gen {{\n{}\n}}",
        left_rules.join("\n|\n"),
        right_rules.join("\n|\n")
    )
}

fn heavy_branch_program(n: usize, depth: usize) -> String {
    let mut branches = Vec::with_capacity(n);
    let p = peano(depth);
    for i in 0..n {
        branches.push(format!(
            "[a -> (cons {p} {p}) ; add ; $x -> (branch{i} $x)]"
        ));
    }
    format!(
        "{}\n\nrel heavy_or {{\n{}\n}}",
        add_program(),
        branches.join("\n|\n")
    )
}

fn inline_gen(n: usize) -> String {
    let mut rules = Vec::with_capacity(n);
    for i in 0..n {
        rules.push(format!("a -> k{i}"));
    }
    rules.join(" | ")
}

fn perm_constraint_program(n: usize) -> String {
    let theory = r#"theory perm_theory {
    constraint neq/2
    (neq $x $x) <=> fail.
    (neq z (s $y)) <=> .
    (neq (s $x) z) <=> .
    (neq (s $x) (s $y)) <=> (neq $x $y).
}"#;
    let constraints: Vec<String> = (0..n).map(|i| format!("(neq $x {})", peano(i))).collect();

    let mut branches = Vec::new();
    for shift in 0..=n {
        let mut rotated = Vec::with_capacity(n);
        for j in 0..n {
            rotated.push(constraints[(j + shift) % n].clone());
        }
        branches.push(format!("$x {{ {} }} -> $x", rotated.join(", ")));
    }
    format!(
        "{}\n\nrel perm_test {{\n{}\n}}",
        theory,
        branches.join("\n|\n")
    )
}

fn expand_template(name: &str) -> String {
    match name {
        "PROGRAM_ADD" => return add_program().to_string(),
        "PROGRAM_EVEN_ODD" => return even_odd_program().to_string(),
        "PROGRAM_EQ_NEQ" => return eq_neq_program().to_string(),
        "PROGRAM_RANGES" => return range_program().to_string(),
        "PROGRAM_PEEL" => return peel_program().to_string(),
        "PROGRAM_WIDE_INC" => return wide_inc_program().to_string(),
        "PROGRAM_TREECALC" => return treecalc_program().to_string(),
        "PROGRAM_TREECALC_SYNTH" => return treecalc_synth_program().to_string(),
        _ => {}
    }

    let parts: Vec<&str> = name.split(':').collect();
    match parts.as_slice() {
        ["PEANO", n] => peano(n.parse().expect("PEANO expects integer")),
        ["NESTED", base, depth] => nested(base, depth.parse().expect("NESTED depth integer")),
        ["OR_PROGRAM", branches] => or_program(branches.parse().expect("OR_PROGRAM integer")),
        ["CHAIN_PROGRAM", len] => chain_program(len.parse().expect("CHAIN_PROGRAM integer")),
        ["CHAIN_QUERY", len] => chain_query(len.parse().expect("CHAIN_QUERY integer")),
        ["DISPATCH_PROGRAM", n] => dispatch_program(n.parse().expect("DISPATCH_PROGRAM integer")),
        ["DISPATCH_CHAIN_QUERY", n] => {
            dispatch_chain_query(n.parse().expect("DISPATCH_CHAIN_QUERY integer"))
        }
        ["MANY_TINY_RELS_PROGRAM", n] => {
            many_tiny_rels_program(n.parse().expect("MANY_TINY_RELS_PROGRAM integer"))
        }
        ["MANY_TINY_RELS_QUERY", n] => {
            many_tiny_rels_query(n.parse().expect("MANY_TINY_RELS_QUERY integer"))
        }
        ["WIDE_TERM", width, depth] => wide_term(
            width.parse().expect("WIDE_TERM width integer"),
            depth.parse().expect("WIDE_TERM depth integer"),
        ),
        ["WIDE_MATCH_PROGRAM", n] => {
            wide_match_program(n.parse().expect("WIDE_MATCH_PROGRAM integer"))
        }
        ["NONLINEAR_MATCH_PROGRAM", n] => {
            nonlinear_match_program(n.parse().expect("NONLINEAR_MATCH_PROGRAM integer"))
        }
        ["GRAPH_REACH_PROGRAM", n] => {
            graph_reach_program(n.parse().expect("GRAPH_REACH_PROGRAM integer"))
        }
        ["LEFT_REC_PROGRAM", n] => left_rec_program(n.parse().expect("LEFT_REC_PROGRAM integer")),
        ["JOIN_PROGRAM", left, right, overlap] => join_program(
            left.parse().expect("JOIN_PROGRAM left integer"),
            right.parse().expect("JOIN_PROGRAM right integer"),
            overlap.parse().expect("JOIN_PROGRAM overlap integer"),
        ),
        ["HEAVY_BRANCH_PROGRAM", n, depth] => heavy_branch_program(
            n.parse().expect("HEAVY_BRANCH_PROGRAM n integer"),
            depth.parse().expect("HEAVY_BRANCH_PROGRAM depth integer"),
        ),
        ["INLINE_GEN", n] => inline_gen(n.parse().expect("INLINE_GEN integer")),
        ["PERM_CONSTRAINT_PROGRAM", n] => {
            perm_constraint_program(n.parse().expect("PERM_CONSTRAINT_PROGRAM integer"))
        }
        _ => panic!("unknown template '{{{{{name}}}}}'"),
    }
}

fn expand_templates(input: &str) -> String {
    let mut out = input.to_string();
    loop {
        let Some(start) = out.find("{{") else {
            return out;
        };
        let tail = &out[start + 2..];
        let Some(rel_end) = tail.find("}}") else {
            panic!("unterminated template in: {out}");
        };
        let end = start + 2 + rel_end;
        let key = out[start + 2..end].trim().to_string();
        let replacement = expand_template(&key);
        out.replace_range(start..end + 2, &replacement);
    }
}

fn env_var(name: &str) -> Option<String> {
    env::var(name)
        .ok()
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
}

fn command_stdout(cmd: &str, args: &[&str]) -> Option<String> {
    Command::new(cmd)
        .args(args)
        .output()
        .ok()
        .and_then(|o| {
            if o.status.success() {
                Some(String::from_utf8_lossy(&o.stdout).trim().to_string())
            } else {
                None
            }
        })
        .filter(|s| !s.is_empty())
}

fn detect_cpu_model() -> Option<String> {
    if let Some(cpu) = env_var("RWLOG_PERF_CPU") {
        return Some(cpu);
    }
    if let Ok(cpuinfo) = fs::read_to_string("/proc/cpuinfo") {
        if let Some(line) = cpuinfo.lines().find(|l| l.starts_with("model name")) {
            if let Some((_, rhs)) = line.split_once(':') {
                let model = rhs.trim();
                if !model.is_empty() {
                    return Some(model.to_string());
                }
            }
        }
    }
    env_var("PROCESSOR_IDENTIFIER")
}

fn build_environment_fingerprint() -> EnvironmentFingerprint {
    let rustc_version =
        command_stdout("rustc", &["--version"]).unwrap_or_else(|| "rustc <unknown>".to_string());

    let timestamp_unix_s = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);

    EnvironmentFingerprint {
        os: env::consts::OS.to_string(),
        arch: env::consts::ARCH.to_string(),
        cpu_model: detect_cpu_model(),
        rustc_version,
        rustflags: env_var("RUSTFLAGS"),
        timestamp_unix_s,
        hostname: env_var("HOSTNAME"),
        git_sha: env_var("GITHUB_SHA")
            .or_else(|| env_var("RWLOG_GIT_SHA"))
            .or_else(|| command_stdout("git", &["rev-parse", "HEAD"])),
        github_run_id: env_var("GITHUB_RUN_ID"),
        github_job: env_var("GITHUB_JOB"),
        github_ref: env_var("GITHUB_REF"),
        run_id: env_var("RWLOG_PERF_RUN_ID"),
    }
}
