export const yCombinator = f => (g => g(g))(g => f((x) => g(g)(x)));

