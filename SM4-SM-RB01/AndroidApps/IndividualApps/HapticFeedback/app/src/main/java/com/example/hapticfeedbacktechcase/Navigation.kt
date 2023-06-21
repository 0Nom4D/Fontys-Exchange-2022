package com.example.hapticfeedbacktechcase

import android.os.Build
import android.os.Vibrator
import androidx.annotation.RequiresApi

import androidx.compose.material.ScaffoldState
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier

import androidx.navigation.NavHostController
import androidx.navigation.compose.NavHost
import androidx.navigation.compose.composable

import com.example.hapticfeedbacktechcase.views.CompositionResearch
import com.example.hapticfeedbacktechcase.views.HapticResearch
import com.example.hapticfeedbacktechcase.views.VibrationResearch

@RequiresApi(Build.VERSION_CODES.S)
@Composable
fun Navigation(vibrator: Vibrator, scaffoldState: ScaffoldState, navController: NavHostController, modifier: Modifier = Modifier) {
    NavHost(navController = navController, startDestination = Screen.HapticResearch.route) {
        composable(route = Screen.HapticResearch.route) {
            HapticResearch(scaffoldState, modifier)
        }

        composable(route = Screen.CompositionResearch.route) {
            CompositionResearch(vibrator, modifier)
        }

        composable(route = Screen.VibrationResearch.route) {
            VibrationResearch(vibrator, modifier)
        }
    }
}
