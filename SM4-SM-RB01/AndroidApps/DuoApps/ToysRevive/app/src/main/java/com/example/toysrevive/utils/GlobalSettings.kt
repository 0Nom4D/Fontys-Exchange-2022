package com.example.toysrevive.utils

import android.net.Uri
import android.util.Log

import androidx.compose.material.ExperimentalMaterialApi
import androidx.compose.material.ModalBottomSheetState
import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.MutableState

import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.snapshots.SnapshotStateList
import androidx.compose.runtime.toMutableStateList

import com.example.toysrevive.R
import com.example.toysrevive.models.*

object GlobalSettings {
    var canBeAuthenticateWithFinderPrint: Boolean = false
    var isFingerprintProtected: Boolean = false

    var currentDetailedToy: MutableState<ToyCard?> = mutableStateOf(null)
    var isToyDescription = mutableStateOf(false)

    var cardNbLimit = mutableStateOf(0)
    var isCardLimitEnabled = false
    var currentSwipedCards = 0

    val currentUser = GivingUser("Arthur", "Adam", "Tutur", "5612JP", 22, "PHONE NUMBER")
    var availableToys = mutableListOf(
        ToyCard("Wood plane", "This is a wood plane", listOf(R.drawable.woodplane, R.drawable.woodplane, R.drawable.woodplane), ObsolescenceState.BRAND_NEW, ToyKind.WOOD_TOY, currentUser),
        ToyCard("Hotwheels Cars", "This is a toy card", listOf(R.drawable.startreck), ObsolescenceState.BRAND_NEW, ToyKind.VIDEO_GAME, currentUser),
        ToyCard("Action figures", "This is some action figures", listOf(R.drawable.startreck), ObsolescenceState.USED, ToyKind.OTHER, currentUser),
        ToyCard("Puzzle", "This is a puzzle", listOf(R.drawable.startreck), ObsolescenceState.USED_BUT_NEW, ToyKind.BOARD_GAME, currentUser),
        ToyCard("Old board game", "This is an old board game", listOf(R.drawable.startreck), ObsolescenceState.BAD, ToyKind.DINOSAURS, currentUser),
        ToyCard("Very old board game", "This is an very old board game", listOf(R.drawable.startreck), ObsolescenceState.VERY_BAD, ToyKind.CARS, currentUser)
    )

    var likedToys = mutableStateListOf<ToyCard>()

    var filteredToyKind = mutableStateListOf<ToyKind>()

    @OptIn(ExperimentalMaterialApi::class)
    suspend fun showCallbackModal(state: ModalBottomSheetState) {
        state.show()
    }

    /**
     * Creates a new [ToyCard], based on parameters, and adds it into the availability list.
     *
     * @param name The name of the toy
     * @param description The description of the newly created donation ad
     * @param pictures List of Uri for the donation ad
     * @param obsolescenceState Toy obsolescence state
     * @param toyKind Toy kind
     */
    fun createNewToy(name: String, description: String, pictures: List<Uri?>, obsolescenceState: ObsolescenceState, toyKind: ToyKind) {
        availableToys.add(
            ToyCard(name, description, pictures, obsolescenceState, toyKind, currentUser, true)
        )
    }

    fun getFilterName(): String {
        var filterName = ""

        if (filteredToyKind.size == 0)
            return "No filter"
        filteredToyKind.mapIndexed { idx, toyKind ->
            if (filterName != "" && idx != 0) {
                filterName += ", "
            }
            filterName += toyKindCorres[enumValues<ToyKind>().indexOf(toyKind)]
        }
        return filterName
    }

    fun handleToyKind(kind: ToyKind) {
        if (filteredToyKind.contains(kind)) {
            filteredToyKind.remove(kind)
        } else {
            filteredToyKind.add(kind)
        }
    }

    /**
     * Adds a given [toy] to the available toy list.
     *
     * @param toy A [ToyCard] Dataclass instance
     */
    private fun makeToyAvailable(toy: ToyCard) {
        availableToys.add(toy)
    }

    /**
     * Remove [toy] from the list of available toys.
     *
     * @param toy A [ToyCard] Dataclass instance
     */
    private fun removeToyAvailability(toy: ToyCard) {
        availableToys.remove(toy)
    }

    /**
     * Adds [toy] in the [likedToys] mutable list and place it at [idx].
     * Removes it from [availableToys] list.
     *
     * @param toy A [ToyCard] Dataclass instance
     * @param idx Index to store [toy] at
     */
    fun likeToyAndPlaceAt(toy: ToyCard, idx: Int) {
        likedToys.add(idx, toy)
        removeToyAvailability(toy)
    }

    /**
     * Adds [toy] in the [likedToys] mutable list and removes it from [availableToys] list.
     *
     * @param toy A [ToyCard] Dataclass instance
     */
    fun likeToy(toy: ToyCard) {
        likedToys.add(toy)
        removeToyAvailability(toy)
    }

    /**
     * Removes [toy] from the [likedToys] mutable list. Adds it back into the [availableToys] list.
     *
     * @param toy A [ToyCard] Dataclass instance
     */
    fun dislikeToy(toy: ToyCard) {
        likedToys.remove(toy)
        makeToyAvailable(toy)
    }

    /**
     * Checks if the card limitation setting is respected.
     *
     * @return Boolean
     */
    fun doesRespectCardLimitation(): Boolean {
        return !isCardLimitEnabled || (isCardLimitEnabled && currentSwipedCards < cardNbLimit.value)
    }
}