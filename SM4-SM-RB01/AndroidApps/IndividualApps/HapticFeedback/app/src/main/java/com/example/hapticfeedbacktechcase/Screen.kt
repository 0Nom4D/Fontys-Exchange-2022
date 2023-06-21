package com.example.hapticfeedbacktechcase

sealed class Screen(val screenName: String, val route: String, val displayName: String) {
    object HapticResearch : Screen("Haptic Research", "haptic_research", "Haptic Research")
    object VibrationResearch : Screen("Vibration Research", "vibration_research", "Vibration Research")
    object CompositionResearch : Screen("Composition Research", "composition_research", "Composition Research")

}

fun getRouteDisplayName(route: String?) : String? {
    val screenRoutes = listOf(
        Screen.HapticResearch,
        Screen.CompositionResearch,
    )

    if (route == null) {
        return null;
    }

    screenRoutes.forEach { screen ->
        if (screen.route == route) {
            return screen.displayName
        }
    }
    return null;
}
