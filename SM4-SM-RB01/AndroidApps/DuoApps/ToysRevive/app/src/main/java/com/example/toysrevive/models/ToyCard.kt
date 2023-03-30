package com.example.toysrevive.models

import android.net.Uri

import com.example.toysrevive.utils.GlobalSettings

/**
 * Information about a donated toy.
 *
 * @property name Name of the toy
 * @property description Description of the toy
 * @property pictures Pictures of the toy
 * @property obsolescenceState Obsolescence State of the toy
 * @property toyKind Kind of toy
 * @property givingUser Information about the user that is donating the toy
 * @property isCreated Checks if the toy is a newly created toy or a templated one
 * @constructor Creates a new ToyCard class.
 */
class ToyCard {
    var name: String = ""
    var description: String = ""
    var pictures: List<Any?> = listOf()
    var obsolescenceState: ObsolescenceState = ObsolescenceState.NO_STATE
    var toyKind: ToyKind = ToyKind.NO_KIND
    var givingUser: GivingUser = GlobalSettings.currentUser
    var isCreated: Boolean = false

    constructor(name: String, description: String, pictures: List<Uri?>, obsolescenceState: ObsolescenceState, toyKind: ToyKind, givingUser: GivingUser, isCreated: Boolean = true) {
        this.name = name
        this.description = description
        this.pictures = pictures
        this.obsolescenceState = obsolescenceState
        this.toyKind = toyKind
        this.givingUser = givingUser
        this.isCreated = isCreated
    }

    constructor(name: String, description: String, pictures: List<Int?>, obsolescenceState: ObsolescenceState, toyKind: ToyKind, givingUser: GivingUser) {
        this.name = name
        this.description = description
        this.pictures = pictures
        this.obsolescenceState = obsolescenceState
        this.toyKind = toyKind
        this.givingUser = givingUser
    }
}
