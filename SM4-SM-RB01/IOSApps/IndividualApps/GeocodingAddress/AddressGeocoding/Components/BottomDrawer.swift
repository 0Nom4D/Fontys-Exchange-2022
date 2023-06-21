//
//  BottomDrawer.swift
//  AddressGeocoding
//
//  Created by Nom4D on 20/03/2023.
//

import SwiftUI

struct BottomDrawer: View {
    @State private var previousOffset: CGFloat = 225
    @State private var offset: CGFloat = 225
    @State private var isInitialOffsetSet: Bool = false

    @State private var chosenLocation: UUID?

    @EnvironmentObject private var geocoderHandler: GeocoderHandler

    @State private var search: String = ""
    @FocusState private var isFocused: Bool

    var body: some View {
        GeometryReader { proxy in
            ZStack {
                Color(.systemBackground)
                    .onTapGesture {
                        if !geocoderHandler.isDetailed {
                            isFocused = false
                            offset = previousOffset
                        }
                    }
                VStack {
                    Capsule()
                        .frame(width: 100, height: 8)
                        .foregroundColor(Color(.systemGray3))
                        .padding(.top, 7)
                    if !geocoderHandler.isDetailed {
                        SearchBar(text: $geocoderHandler.request)
                            .focused($isFocused)
                        if isFocused == false && geocoderHandler.request == "" {
                            if !geocoderHandler.knownLocations.isEmpty {
                                LocationList(
                                    offset: $offset,
                                    sectionName: "Recent locations",
                                    elementList: Array(geocoderHandler.knownLocations.enumerated())
                                )
                                .onTapGesture {
                                    isFocused = false
                                    offset = previousOffset
                                }
                            } else {
                                Text("You never searched for a location.")
                            }
                        } else if geocoderHandler.request != "" && !geocoderHandler.isDetailed {
                            if !geocoderHandler.lastFetchedLocations.isEmpty {
                                LocationList(offset: $offset, elementList: Array(geocoderHandler.getSearchedLocationsNames().enumerated()))
                                    .onTapGesture {
                                        isFocused = false
                                        offset = previousOffset
                                    }
                            } else {
                                Text("No suggestions found.")
                            }
                        }
                    } else {
                        ElementDetails(
                            locationName: geocoderHandler.currentLocation.name,
                            locationAdditionalName: geocoderHandler.currentLocation.additionalName
                        )
                        .frame(width: UIScreen.main.bounds.width, height: UIScreen.main.bounds.height - (offset + 80), alignment: .topTrailing)
                    }
                    Spacer()
                }
            }
        }
        .offset(y: offset)
        .gesture(
            DragGesture().onChanged { value in
                let startLocation = value.startLocation
                offset = startLocation.y + value.translation.height
                if offset < UIScreen.main.bounds.size.height * 0.1 {
                    offset = UIScreen.main.bounds.size.height * 0.1
                } else if offset > UIScreen.main.bounds.height - 225 {
                    offset = UIScreen.main.bounds.height - 225
                }
            }
        )
        .animation(
            .easeInOut,
            value: offset
        )
        .onChange(of: isFocused, perform: { newValue in
            if (newValue == true) {
                previousOffset = offset
                offset = UIScreen.main.bounds.size.height * 0.1
            }
        })
        .onAppear {
            if !isInitialOffsetSet {
                offset = UIScreen.main.bounds.height - 225
                isInitialOffsetSet = true
            }
        }
        .environmentObject(geocoderHandler)
    }
}

struct BottomDrawer_Previews: PreviewProvider {
    static var previews: some View {
        BottomDrawer()
    }
}
