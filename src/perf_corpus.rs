use crate::chr::{ChrState, NoTheory};
use crate::engine::Engine;
use crate::perf_counters;
use crate::parser::{ChrConstraintBuilder, Parser};
use crate::rel::Rel;
use crate::repl::split_statements;
use crate::term::TermStore;
use crate::work::Env;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::env;
use std::fs;
use std::process::Command;
use std::sync::OnceLock;
use std::time::{SystemTime, UNIX_EPOCH};

pub type CorpusConstraint = ChrState<NoTheory>;
pub const CORPUS_SCHEMA_VERSION: u32 = 1;

#[derive(Clone, Debug, Serialize)]
pub struct EnvironmentFingerprint {
    pub os: String,
    pub arch: String,
    pub cpu_model: Option<String>,
    pub rustc_version: String,
    pub rustflags: Option<String>,
    pub timestamp_unix_s: u64,
    pub hostname: Option<String>,
    pub git_sha: Option<String>,
    pub github_run_id: Option<String>,
    pub github_job: Option<String>,
    pub github_ref: Option<String>,
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

impl CaseCategory {
    pub fn from_str(s: &str) -> Self {
        match s {
            "finite_det" => CaseCategory::FiniteDeterministic,
            "finite_nondet" => CaseCategory::FiniteNondeterministic,
            "recursive" => CaseCategory::Recursive,
            "constraints" => CaseCategory::Constraints,
            "deep_terms" => CaseCategory::DeepTerms,
            "wide_branching" => CaseCategory::WideBranching,
            other => panic!("unknown category '{other}'"),
        }
    }

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

impl CaseTier {
    pub fn from_str(s: &str) -> Self {
        match s {
            "quick" => CaseTier::Quick,
            "stress" => CaseTier::Stress,
            other => panic!("unknown tier '{other}'"),
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            CaseTier::Quick => "quick",
            CaseTier::Stress => "stress",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DeterminismClass {
    Deterministic,
    Nondeterministic,
}

impl DeterminismClass {
    pub fn from_str(s: &str) -> Self {
        match s {
            "deterministic" => DeterminismClass::Deterministic,
            "nondeterministic" => DeterminismClass::Nondeterministic,
            other => panic!("unknown determinism '{other}'"),
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            DeterminismClass::Deterministic => "deterministic",
            DeterminismClass::Nondeterministic => "nondeterministic",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AnswerShape {
    Single,
    Finite,
    PrefixStream,
}

impl AnswerShape {
    pub fn from_str(s: &str) -> Self {
        match s {
            "single" => AnswerShape::Single,
            "finite" => AnswerShape::Finite,
            "prefix_stream" => AnswerShape::PrefixStream,
            other => panic!("unknown answer shape '{other}'"),
        }
    }

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

#[derive(Clone, Copy, Debug, Default, Serialize)]
pub struct ExecutionCounters {
    pub engine_steps: u64,
    pub engine_emits: u64,
    pub engine_continues: u64,
    pub engine_exhausted: u64,
    pub compose_attempts: u64,
    pub compose_successes: u64,
    pub compose_failures: u64,
    pub meet_attempts: u64,
    pub meet_successes: u64,
    pub meet_failures: u64,
}

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
            out.determinism = Some(DeterminismClass::from_str(&d));
        }
        if let Some(shape) = env_var("RWLOG_CORPUS_ANSWER_SHAPE") {
            out.answer_shape = Some(AnswerShape::from_str(&shape));
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
            tier: CaseTier::from_str(&c.tier),
            category: CaseCategory::from_str(&c.category),
            description: c.description,
            program: expand_templates(&c.program),
            query: expand_templates(&c.query),
            mode: RunMode::from_parts(&c.mode, c.mode_limit),
            expected: ExpectedAnswers::from_parts(&c.expected_kind, c.expected_value),
            tags: c.tags.unwrap_or_default(),
            determinism: c
                .determinism
                .as_deref()
                .map(DeterminismClass::from_str)
                .unwrap_or(DeterminismClass::Nondeterministic),
            answer_shape: c
                .answer_shape
                .as_deref()
                .map(AnswerShape::from_str)
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
        (a.tier, a.category, a.determinism.as_str(), &a.id).cmp(&(
            b.tier,
            b.category,
            b.determinism.as_str(),
            &b.id,
        ))
    });
}

pub fn lint_cases(cases: &[CorpusCase]) -> Result<(), String> {
    let (meta, all_cases) = load_meta_and_cases();
    // If caller passed a strict subset, lint full corpus policy and then local invariants for the subset.
    lint_cases_with_meta(&meta, &all_cases)?;
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
        let _ = CaseCategory::from_str(category);
    }
    for category in &meta.require_real_world_tag_in_categories {
        let _ = CaseCategory::from_str(category);
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
                return Err(format!("case '{}' first_n requires mode_limit > 0", case.id));
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

fn execution_counters_from_snapshot(snapshot: perf_counters::PerfCountersSnapshot) -> ExecutionCounters {
    ExecutionCounters {
        engine_steps: snapshot.engine_steps,
        engine_emits: snapshot.engine_emits,
        engine_continues: snapshot.engine_continues,
        engine_exhausted: snapshot.engine_exhausted,
        compose_attempts: snapshot.compose_attempts,
        compose_successes: snapshot.compose_successes,
        compose_failures: snapshot.compose_failures,
        meet_attempts: snapshot.meet_attempts,
        meet_successes: snapshot.meet_successes,
        meet_failures: snapshot.meet_failures,
    }
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
    let (answers, snapshot) = perf_counters::capture(|| run_prepared_inner(case, prepared));
    RunStats {
        answers,
        counters: execution_counters_from_snapshot(snapshot),
    }
}

pub fn run_prepared(case: &CorpusCase, prepared: PreparedCase) -> usize {
    run_prepared_with_stats(case, prepared).answers
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
            let (name, rel) = parser.parse_rel_def(line).expect("parse relation");
            defs.insert(name, rel);
            continue;
        }
        panic!("unsupported corpus statement: {line}");
    }
    defs
}

fn build_env(defs: &HashMap<String, Rel<CorpusConstraint>>) -> Env<CorpusConstraint> {
    let mut env = Env::new();
    for rel in defs.values() {
        if let Rel::Fix(id, body) = rel {
            env = env.bind(*id, body.clone());
        }
    }
    env
}

fn peano(n: usize) -> String {
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

fn expand_template(name: &str) -> String {
    if name == "PROGRAM_ADD" {
        return add_program().to_string();
    }
    if name == "PROGRAM_EVEN_ODD" {
        return even_odd_program().to_string();
    }
    if name == "PROGRAM_EQ_NEQ" {
        return eq_neq_program().to_string();
    }
    if name == "PROGRAM_RANGES" {
        return range_program().to_string();
    }
    if name == "PROGRAM_PEEL" {
        return peel_program().to_string();
    }
    if name == "PROGRAM_TREECALC" {
        return include_str!("../examples/treecalc.txt").to_string();
    }

    let parts: Vec<&str> = name.split(':').collect();
    match parts.as_slice() {
        ["PEANO", n] => peano(n.parse().expect("PEANO expects integer")),
        ["NESTED", base, depth] => nested(base, depth.parse().expect("NESTED depth integer")),
        ["OR_PROGRAM", branches] => or_program(branches.parse().expect("OR_PROGRAM integer")),
        ["CHAIN_PROGRAM", len] => chain_program(len.parse().expect("CHAIN_PROGRAM integer")),
        ["CHAIN_QUERY", len] => chain_query(len.parse().expect("CHAIN_QUERY integer")),
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
    let rustc_version = command_stdout("rustc", &["--version"])
        .unwrap_or_else(|| "rustc <unknown>".to_string());

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
