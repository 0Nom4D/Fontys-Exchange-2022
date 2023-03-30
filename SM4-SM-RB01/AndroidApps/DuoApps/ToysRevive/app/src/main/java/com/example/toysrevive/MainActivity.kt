package com.example.toysrevive

import android.os.Build
import android.os.Bundle

import androidx.appcompat.app.AppCompatActivity

import androidx.activity.compose.setContent
import androidx.annotation.RequiresApi

import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material.*
import androidx.compose.runtime.getValue
import androidx.compose.runtime.rememberCoroutineScope

import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.unit.dp

import androidx.navigation.compose.currentBackStackEntryAsState
import androidx.navigation.compose.rememberNavController

import androidx.biometric.BiometricManager
import androidx.biometric.BiometricPrompt
import androidx.biometric.BiometricManager.Authenticators.BIOMETRIC_STRONG

import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.outlined.Settings

import com.example.toysrevive.ui.theme.ToysReviveTheme
import com.example.toysrevive.ui.theme.getPoppins
import com.example.toysrevive.utils.GlobalSettings
import com.example.toysrevive.widgets.FiltersModal
import com.example.toysrevive.widgets.ToyDescriptionModal
import com.example.toysrevive.widgets.ToysReviveBottomAppBar

import kotlinx.coroutines.launch
import kotlinx.coroutines.CoroutineScope

@OptIn(ExperimentalMaterialApi::class)
class MainActivity : AppCompatActivity() {
    @RequiresApi(Build.VERSION_CODES.R)
    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        setContent {
            ToysReviveTheme {
                val navController = rememberNavController()
                val scaffoldState = rememberScaffoldState()

                val navBackStackEntry by navController.currentBackStackEntryAsState()
                val currentRoute = navBackStackEntry?.destination?.route

                val bottomSheetState = rememberModalBottomSheetState(
                    initialValue = ModalBottomSheetValue.Hidden,
                    skipHalfExpanded = true,
                )

                val coroutineScope = rememberCoroutineScope()

                val biometricManager = BiometricManager.from(this)
                when (biometricManager.canAuthenticate(BIOMETRIC_STRONG)) {
                    BiometricManager.BIOMETRIC_SUCCESS -> GlobalSettings.canBeAuthenticateWithFinderPrint = true
                    BiometricManager.BIOMETRIC_ERROR_NO_HARDWARE -> {}
                    BiometricManager.BIOMETRIC_ERROR_HW_UNAVAILABLE -> {}
                    BiometricManager.BIOMETRIC_ERROR_NONE_ENROLLED -> {}
                    BiometricManager.BIOMETRIC_ERROR_SECURITY_UPDATE_REQUIRED -> {}
                    BiometricManager.BIOMETRIC_ERROR_UNSUPPORTED -> {}
                    BiometricManager.BIOMETRIC_STATUS_UNKNOWN -> {}
                }

                ModalBottomSheetLayout(
                    sheetState = bottomSheetState,
                    sheetShape = RoundedCornerShape(topStart = 15.dp, topEnd = 15.dp),
                    sheetContent = {
                        if (!GlobalSettings.isToyDescription.value) FiltersModal() else ToyDescriptionModal()
                    }
                ) {
                    Scaffold(
                        modifier = Modifier.fillMaxSize(),
                        topBar = {
                            TopAppBar(
                                title = {
                                    getRouteDisplayName(currentRoute)?.let {
                                        Text(it, fontFamily = getPoppins())
                                    }
                                },
                                backgroundColor = MaterialTheme.colors.background,
                                elevation = 0.dp,
                                actions = {
                                    if (currentRoute == Screen.SwipeScreen.route) {
                                        Card(
                                            shape = RoundedCornerShape(10.dp),
                                            backgroundColor = MaterialTheme.colors.surface
                                        ) {
                                            IconButton(onClick = {
                                                GlobalSettings.isToyDescription.value = false
                                                if (GlobalSettings.canBeAuthenticateWithFinderPrint && GlobalSettings.isFingerprintProtected) {
                                                    showBiometricPrompt(coroutineScope, scaffoldState, bottomSheetState)
                                                } else {
                                                    coroutineScope.launch {
                                                        GlobalSettings.showCallbackModal(bottomSheetState)
                                                    }
                                                }
                                            }) {
                                                Icon(
                                                    Icons.Outlined.Settings,
                                                    tint = Color.Black,
                                                    contentDescription = ""
                                                )
                                            }
                                        }
                                    }
                                }
                            )
                        },
                        bottomBar = { ToysReviveBottomAppBar(navController = navController) },
                        scaffoldState = scaffoldState
                    ) {
                        Navigation(scaffoldState, navController, bottomSheetState, Modifier.padding(it))
                    }
                }
            }
        }
    }

    private fun showBiometricPrompt(coroutineScope: CoroutineScope, scaffoldState: ScaffoldState, bottomSheetState: ModalBottomSheetState) {
        val promptInfo = BiometricPrompt.PromptInfo.Builder()
            .setTitle("Authenticate to get to settings")
            .setSubtitle("This settings section is protected by biometric prompt. Please authenticate to access settings.")
            .setNegativeButtonText("Cancel")
            .setConfirmationRequired(true)
            .setAllowedAuthenticators(BIOMETRIC_STRONG)
            .build()

        val biometricPrompt = BiometricPrompt(
            this@MainActivity,
            object : BiometricPrompt.AuthenticationCallback() {
                override fun onAuthenticationError(
                    errorCode: Int,
                    errString: CharSequence
                ) {
                    super.onAuthenticationError(errorCode, errString)
                    coroutineScope.launch {
                        when (scaffoldState.snackbarHostState.showSnackbar("Authentication failed. We're unable to let you access settings..", "")) {
                            else -> {}
                        }
                    }
                }

                override fun onAuthenticationSucceeded(
                    result: BiometricPrompt.AuthenticationResult
                ) {
                    super.onAuthenticationSucceeded(result)
                    coroutineScope.launch {
                        GlobalSettings.showCallbackModal(bottomSheetState)
                    }
                }

                override fun onAuthenticationFailed() {
                    super.onAuthenticationFailed()
                    coroutineScope.launch {
                        when (scaffoldState.snackbarHostState.showSnackbar("Authentication failed. We're unable to let you access settings..", "")) {
                            else -> {}
                        }
                    }
                }
            }
        )

        biometricPrompt.authenticate(promptInfo)
    }
}
