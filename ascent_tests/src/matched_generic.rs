/// Generic trait-based matched! handler system
///
/// This allows the return type to actually drive behavior, rather than just
/// being a type annotation. Users can call matched!(MatchedContext::<Type>)
/// and get different behavior based on Type.

use std::marker::PhantomData;

/// Trait for handling matched! macro invocations with type-driven behavior
pub trait MatchedHandler {
    /// The output type this handler produces
    type Output;

    /// Handle a matched! invocation
    ///
    /// # Parameters
    /// - `rel_names`: Names of relations used in the rule body (before matched!)
    /// - `head_vars`: Variables extracted from the rule head
    /// - `rel_names2`: Duplicate of rel_names (for API compatibility)
    /// - `rel_args`: Arguments for each relation clause
    /// - `operator`: The operator context (e.g., "for x in", "if", "let x =")
    /// - `rel_arg_values`: Runtime values of relation arguments
    /// - `head_var_values`: Runtime values of head variables
    fn handle(
        rel_names: &[&str],
        head_vars: &[&str],
        rel_names2: &[&str],
        rel_args: &[&str],
        operator: &str,
        rel_arg_values: &[String],
        head_var_values: &[String],
    ) -> Self::Output;
}

/// Generic context for matched! handlers
///
/// Use this as the handler in matched! calls:
/// ```ignore
/// matched!(MatchedContext::<usize>)
/// matched!(MatchedContext::<bool>)
/// matched!(MatchedContext::<Vec<(String, String)>>)
/// ```
///
/// The type parameter determines what operation is performed and what is returned.
pub struct MatchedContext<T>(PhantomData<T>);

impl<T> MatchedContext<T> {
    /// Generic handler that dispatches based on the output type
    ///
    /// This method can be called directly or through the trait bound.
    /// The return type T must implement MatchedHandler for MatchedContext<T>.
    pub fn handle(
        rel_names: &[&str],
        head_vars: &[&str],
        rel_names2: &[&str],
        rel_args: &[&str],
        operator: &str,
        rel_arg_values: &[String],
        head_var_values: &[String],
    ) -> T
    where
        MatchedContext<T>: MatchedHandler<Output = T>,
    {
        <MatchedContext<T> as MatchedHandler>::handle(
            rel_names, head_vars, rel_names2, rel_args, operator, rel_arg_values, head_var_values
        )
    }
}

// ============================================================================
// Utility function for string reconstruction
// ============================================================================

/// Constructs a string representation of a matched! rule
///
/// This function reconstructs the rule syntax from the metadata passed by the macro.
fn construct_matched_string(
    rel_names: &[&str],
    head_vars: &[&str],
    _rel_names2: &[&str],
    rel_args: &[&str],
    operator: &str,
) -> String {
    let mut result = String::new();

    // Construct the rule head
    result.push_str("result(");
    if !head_vars.is_empty() {
        result.push_str(&head_vars.join(", "));
    } else {
        result.push_str("...");
    }
    result.push_str(") <--\n");

    // Add each relation clause
    for (name, args) in rel_names.iter().zip(rel_args.iter()) {
        result.push_str("    ");
        result.push_str(name);
        result.push('(');
        result.push_str(args);
        result.push_str("),\n");
    }

    // Add the matched! invocation
    result.push_str("    ");
    result.push_str(operator);
    result.push_str(" matched!");

    result
}

// ============================================================================
// Standard implementations for common types
// ============================================================================

/// Return the count of clauses before the matched! invocation
impl MatchedHandler for MatchedContext<usize> {
    type Output = usize;

    fn handle(
        rel_names: &[&str],
        _head_vars: &[&str],
        _rel_names2: &[&str],
        _rel_args: &[&str],
        _operator: &str,
        _rel_arg_values: &[String],
        _head_var_values: &[String],
    ) -> usize {
        rel_names.len()
    }
}

/// Return whether there are any clauses before the matched! invocation
impl MatchedHandler for MatchedContext<bool> {
    type Output = bool;

    fn handle(
        rel_names: &[&str],
        _head_vars: &[&str],
        _rel_names2: &[&str],
        _rel_args: &[&str],
        _operator: &str,
        _rel_arg_values: &[String],
        _head_var_values: &[String],
    ) -> bool {
        !rel_names.is_empty()
    }
}

/// Return a list of (relation_name, arguments) pairs
impl MatchedHandler for MatchedContext<Vec<(String, String)>> {
    type Output = Vec<(String, String)>;

    fn handle(
        rel_names: &[&str],
        _head_vars: &[&str],
        _rel_names2: &[&str],
        rel_args: &[&str],
        _operator: &str,
        _rel_arg_values: &[String],
        _head_var_values: &[String],
    ) -> Vec<(String, String)> {
        rel_names
            .iter()
            .zip(rel_args.iter())
            .map(|(name, args)| (name.to_string(), args.to_string()))
            .collect()
    }
}

/// Return Some(count) if there are clauses, None if empty
impl MatchedHandler for MatchedContext<Option<usize>> {
    type Output = Option<usize>;

    fn handle(
        rel_names: &[&str],
        _head_vars: &[&str],
        _rel_names2: &[&str],
        _rel_args: &[&str],
        _operator: &str,
        _rel_arg_values: &[String],
        _head_var_values: &[String],
    ) -> Option<usize> {
        if rel_names.is_empty() {
            None
        } else {
            Some(rel_names.len())
        }
    }
}

/// Return the reconstructed rule string representation
impl MatchedHandler for MatchedContext<String> {
    type Output = String;

    fn handle(
        rel_names: &[&str],
        head_vars: &[&str],
        rel_names2: &[&str],
        rel_args: &[&str],
        operator: &str,
        _rel_arg_values: &[String],
        _head_var_values: &[String],
    ) -> String {
        construct_matched_string(rel_names, head_vars, rel_names2, rel_args, operator)
    }
}

/// Return a list of all relation names
impl MatchedHandler for MatchedContext<Vec<String>> {
    type Output = Vec<String>;

    fn handle(
        rel_names: &[&str],
        _head_vars: &[&str],
        _rel_names2: &[&str],
        _rel_args: &[&str],
        _operator: &str,
        _rel_arg_values: &[String],
        _head_var_values: &[String],
    ) -> Vec<String> {
        rel_names.iter().map(|s| s.to_string()).collect()
    }
}

// ============================================================================
// Example custom type with its handler
// ============================================================================

/// Example of a custom analysis type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClauseAnalysis {
    /// Number of clauses
    pub count: usize,
    /// Names of all relations
    pub names: Vec<String>,
    /// Total complexity (sum of argument counts)
    pub complexity: usize,
    /// The operator context
    pub operator: String,
}

impl MatchedHandler for MatchedContext<ClauseAnalysis> {
    type Output = ClauseAnalysis;

    fn handle(
        rel_names: &[&str],
        _head_vars: &[&str],
        _rel_names2: &[&str],
        rel_args: &[&str],
        operator: &str,
        _rel_arg_values: &[String],
        _head_var_values: &[String],
    ) -> ClauseAnalysis {
        ClauseAnalysis {
            count: rel_names.len(),
            names: rel_names.iter().map(|s| s.to_string()).collect(),
            complexity: rel_args.iter().map(|a| a.split(',').count()).sum(),
            operator: operator.to_string(),
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matched_context_usize() {
        let result = MatchedContext::<usize>::handle(
            &["testa", "testb"],
            &["x", "y"],
            &["testa", "testb"],
            &["a", "b, c"],
            "if",
            &[],
            &[],
        );
        assert_eq!(result, 2);
    }

    #[test]
    fn test_matched_context_bool() {
        let result = MatchedContext::<bool>::handle(
            &["testa"],
            &[],
            &["testa"],
            &["a"],
            "if",
            &[],
            &[],
        );
        assert_eq!(result, true);

        let result = MatchedContext::<bool>::handle(
            &[],
            &[],
            &[],
            &[],
            "if",
            &[],
            &[],
        );
        assert_eq!(result, false);
    }

    #[test]
    fn test_matched_context_vec_tuple() {
        let result = MatchedContext::<Vec<(String, String)>>::handle(
            &["testa", "testb"],
            &["name", "args"],
            &["testa", "testb"],
            &["obj1", "obj2, obj1"],
            "for (name, args) in",
            &[],
            &[],
        );

        assert_eq!(result.len(), 2);
        assert_eq!(result[0], ("testa".to_string(), "obj1".to_string()));
        assert_eq!(result[1], ("testb".to_string(), "obj2, obj1".to_string()));
    }

    #[test]
    fn test_matched_context_option() {
        let result = MatchedContext::<Option<usize>>::handle(
            &["testa", "testb"],
            &[],
            &["testa", "testb"],
            &["a", "b"],
            "if let Some(count) =",
            &[],
            &[],
        );
        assert_eq!(result, Some(2));

        let result = MatchedContext::<Option<usize>>::handle(
            &[],
            &[],
            &[],
            &[],
            "if let Some(count) =",
            &[],
            &[],
        );
        assert_eq!(result, None);
    }

    #[test]
    fn test_matched_context_string() {
        let result = MatchedContext::<String>::handle(
            &["testa"],
            &[],
            &["testa"],
            &["a"],
            "if",
            &[],
            &[],
        );

        assert!(result.contains("result(...)"));
        assert!(result.contains("testa(a)"));
        assert!(result.contains("if matched!"));
    }

    #[test]
    fn test_matched_context_vec_string() {
        let result = MatchedContext::<Vec<String>>::handle(
            &["testa", "testb", "testc"],
            &[],
            &["testa", "testb", "testc"],
            &["a", "b", "c"],
            "if",
            &[],
            &[],
        );

        assert_eq!(result, vec!["testa", "testb", "testc"]);
    }

    #[test]
    fn test_clause_analysis() {
        let result = MatchedContext::<ClauseAnalysis>::handle(
            &["testa", "testb"],
            &["x"],
            &["testa", "testb"],
            &["a", "b, c"],
            "let x =",
            &[],
            &[],
        );

        assert_eq!(result.count, 2);
        assert_eq!(result.names, vec!["testa", "testb"]);
        assert_eq!(result.complexity, 3); // 1 arg + 2 args
        assert_eq!(result.operator, "let x =");
    }

    #[test]
    fn test_generic_handle_method() {
        // Test that the generic handle method works with type inference
        let result: usize = MatchedContext::handle(
            &["testa"],
            &[],
            &["testa"],
            &["a"],
            "if",
            &[],
            &[],
        );
        assert_eq!(result, 1);

        let result: bool = MatchedContext::handle(
            &["testa"],
            &[],
            &["testa"],
            &["a"],
            "if",
            &[],
            &[]
        );
        assert_eq!(result, true);
    }
}
